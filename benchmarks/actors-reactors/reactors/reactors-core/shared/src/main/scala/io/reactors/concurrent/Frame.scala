package io.reactors
package concurrent



import java.util.concurrent.atomic._
import java.util.concurrent.ConcurrentHashMap
import scala.annotation.tailrec
import scala.collection._
import io.reactors.common.UnrolledRing
import io.reactors.common.Monitor



/** Placeholder for the reactor's state.
 */
final class Frame(
  val uid: Long,
  val proto: Proto[Reactor[_]],
  val scheduler: Scheduler,
  val reactorSystem: ReactorSystem
) extends Identifiable {
  private[reactors] val monitor = new Monitor
  private[reactors] val idCounter = new AtomicLong(0L)
  private[reactors] var nonDaemonCount = 0
  private[reactors] var active = false
  private[reactors] val activeCount = new AtomicInteger(0)
  private[reactors] var lifecycleState: Frame.LifecycleState = Frame.Fresh
  private[reactors] val pendingQueues = new UnrolledRing[Connector[_]]
  private[reactors] val sysEmitter = new Events.Emitter[SysEvent]

  @volatile var reactor: Reactor[_] = _
  @volatile var name: String = _
  @volatile var url: ReactorUrl = _
  @volatile var defaultConnector: Connector[_] = _
  @volatile var internalConnector: Connector[_] = _
  @volatile var schedulerState: Scheduler.State = _
  @volatile private var spins = 0

  // Speculation state.
  private[reactors] var seed = (uid << 32) | System.identityHashCode(this)
  private[reactors] var scheduleCount = 0
  private[reactors] var sampleCount = 0
  private[reactors] var histogram: Array[Int] = null
  private[reactors] var samplingFrequency: Double = 0.0
  private[reactors] var spinSpeculation = 0

  // Spindown state.
  // private[reactors] var spindown =
  //   reactorSystem.bundle.schedulerConfig.spindownInitial
  // private[reactors] val schedulerConfig = reactorSystem.bundle.schedulerConfig
  // private[reactors] var totalBatches = 0L
  // private[reactors] var totalSpindownScore = 0L
  // private[reactors] var random = new Random

  def openConnector[@spec(Int, Long, Double) Q: Arrayable](
    channelName: String,
    factory: EventQueue.Factory,
    isDaemon: Boolean,
    shortcut: Boolean,
    extras: immutable.Map[Class[_], Any]
  ): Connector[Q] = {
    // Note: invariant is that there is always at most one thread calling this method.
    // However, they may be multiple threads updating the frame map.
    var newConnector: Connector[Q] = null
    while (newConnector == null) {
      // 1. Prepare and ensure a unique id for the channel.
      val uid = idCounter.getAndIncrement()

      // 2. Find a unique name.
      val info = reactorSystem.frames.forName(name)
      assert(info != null, name)
      @tailrec def chooseName(count: Long): String = {
        val n = s"channel-$uid-$count"
        if (info.connectors.contains(n)) chooseName(count + 1)
        else n
      }
      val uname = {
        if (channelName != null) {
          info.connectors.get(channelName) match {
            case Some(c: Connector[_]) =>
              throw new IllegalStateException(s"Channel '$channelName' already exists.")
            case _ =>
              channelName
          }
        } else chooseName(0L)
      }

      // 3. Instantiate a connector.
      val queue = factory.newInstance[Q]
      val chanUrl = ChannelUrl(url, uname)
      val localChan = new Channel.Local[Q](reactorSystem, uid, this, shortcut)
      val chan = {
        if (reactorSystem.usingLocalChannels) new Channel.Shared(chanUrl, localChan)
        else {
          val ch = new Channel.Shared(chanUrl, null)
          ch.resolve(reactorSystem)
          ch
        }
      }
      val conn = new Connector(
        chan, localChan, queue, this, mutable.Map(extras.toSeq: _*), isDaemon)
      val ninfo = Frame.Info(this, info.connectors + (uname -> conn))
      localChan.connector = conn

      // 4. Add connector to the global list.
      if (reactorSystem.frames.tryReplace(name, info, ninfo)) {
        newConnector = conn

        // 5. If there were listeners under that connector name, trigger them.
        info.connectors.get(uname) match {
          case Some(listeners: List[Channel[Channel[Q]]] @unchecked) =>
            for (ch <- listeners) ch ! conn.channel
          case _ =>
        }
      }
    }

    // 6. Update count of non-daemon channels.
    if (!isDaemon) nonDaemonCount += 1

    // 7. Return connector.
    newConnector
  }

  /** Atomically schedules the frame for execution, unless already scheduled.
   */
  def activate(scheduleEvenIfActive: Boolean) {
    var mustSchedule = false
    monitor.synchronized {
      if (!active || scheduleEvenIfActive) {
        active = true
        mustSchedule = true
      }
    }
    if (mustSchedule) scheduler.schedule(this)
  }

  def enqueueEvent[@spec(Int, Long, Double) T](conn: Connector[T], x: T) {
    // 1. Add the event to the event queue.
    val size = conn.queue.enqueue(x)

    // 2. Check if the frame should be scheduled for execution.
    var mustSchedule = false
    if (size == 1) monitor.synchronized {
      // 3. Add the queue to pending queues.
      pendingQueues.enqueue(conn)

      // 4. Schedule the frame for later execution.
      if (!active && lifecycleState != Frame.Terminated) {
        active = true
        mustSchedule = true
      }
    }
    if (mustSchedule) scheduler.schedule(this)
  }

  @tailrec
  private def assertIsolated() {
    val count = activeCount.get
    if (count != 0) assert(false, s"Not isolated, count was: " + count)
    else if (!activeCount.compareAndSet(0, 1)) assertIsolated()
  }

  def executeBatch() {
    scheduler.preschedule(reactorSystem)

    // This method cannot be executed inside another reactor.
    if (Reactor.currentReactor != null) {
      throw new IllegalStateException(
        s"Cannot execute reactor inside another reactor: ${Reactor.currentReactor}.")
    }

    // 1. Check the state and ensure that this is the only thread running.
    // This method can only be called if the frame is in the "active" state, and no
    // other thread is executing the frame.
    assert(active)
    assertIsolated()

    // 2. Process a batch of events.
    var throwable: Throwable = null
    try {
      isolateAndProcessBatch()
    } catch {
      case t: Throwable => throwable = t
    } finally {
      // Set active count back to 0, *before* re-scheduling the reactor.
      activeCount.set(0)

      // Set the execution state to false if no more events, or otherwise re-schedule.
      var mustSchedule = false
      monitor.synchronized {
        if (pendingQueues.nonEmpty && !hasTerminated) {
          mustSchedule = true
        } else {
          active = false
        }
      }
      if (mustSchedule) scheduler.schedule(this)

      // 3. Piggyback the worker thread to do some useful work.
      scheduler.postschedule(reactorSystem, throwable)
      if (throwable != null) throw throwable
    }
  }

  private def isolateAndProcessBatch() {
    try {
      Reactor.currentFrame = this
      processBatch()
    } catch {
      case t: Throwable =>
        try {
          if (!hasTerminated) {
            if (reactor != null) sysEmitter.react(ReactorDied(t))
          }
        } finally {
          checkTerminated(true)
        }
        throw t
    } finally {
      Reactor.currentFrame = null
      Reactor.onContextSwitch()
    }
  }

  private def checkFresh() {
    var runCtor = false
    monitor.synchronized {
      if (lifecycleState == Frame.Fresh) {
        lifecycleState = Frame.Running
        runCtor = true
      }
    }
    if (runCtor) {
      reactorSystem.debugApi.reactorStarted(this)
      reactor = proto.create()
      samplingFrequency = computeInitialSamplingFrequency()
      sysEmitter.react(ReactorStarted)
    }
  }

  private def popNextPending(): Connector[_] = monitor.synchronized {
    if (pendingQueues.nonEmpty) pendingQueues.dequeue()
    else null
  }

  // private def processEvents() {
  //   schedulerState.onBatchStart(this)

  //   // Precondition: there is at least one pending event.
  //   // Return value:
  //   // - `false` iff stopped by preemption
  //   // - `true` iff stopped because there are no events
  //   @tailrec def drain(c: Connector[_]): Boolean = {
  //     val remaining = c.dequeue()
  //     if (schedulerState.onBatchEvent(this)) {
  //       // Need to consume some more.
  //       if (remaining > 0 && !c.localChannel.isSealed) {
  //         drain(c)
  //       } else {
  //         val nc = popNextPending()
  //         if (nc != null) drain(nc)
  //         else true
  //       }
  //     } else {
  //       // Done consuming -- see if the connector needs to be enqueued.
  //       if (remaining > 0 && !c.localChannel.isSealed) monitor.synchronized {
  //         pendingQueues.enqueue(c)
  //       }
  //       false
  //     }
  //   }

  //   var nc = popNextPending()
  //   var spindownScore = 0
  //   while (nc != null) {
  //     if (drain(nc)) {
  //       // Wait a bit for additional events, since preemption is expensive.
  //       nc = null
  //       spins = spindown
  //       while (spins > 0) {
  //         spins -= 1
  //         if (spins % 10 == 0) {
  //           nc = popNextPending()
  //           if (nc != null) spins = 0
  //         }
  //       }
  //       if (nc != null) spindownScore += 1
  //     } else {
  //       nc = null
  //     }
  //   }

  //   // Adjust spindown stochastically.
  //   totalBatches += 1
  //   totalSpindownScore += spindownScore
  //   val spindownMutationRate = schedulerConfig.spindownMutationRate
  //   if (random.nextDouble() < spindownMutationRate || spindownScore >= 1) {
  //     var spindownCoefficient = 1.0 * totalSpindownScore / totalBatches
  //     val threshold = schedulerConfig.spindownTestThreshold
  //     val iters = schedulerConfig.spindownTestIterations
  //     if (totalBatches >= threshold) {
  //       spindownCoefficient +=
  //         math.max(0.0, 1.0 - (totalBatches - threshold) / iters)
  //     }
  //     spindownCoefficient = math.min(1.0, spindownCoefficient)
  //     spindown = (schedulerConfig.spindownMax * spindownCoefficient).toInt
  //   }
  //   spindown -= (spindown / schedulerConfig.spindownCooldownRate + 1)
  //   spindown = math.max(schedulerConfig.spindownMin, spindown)
  // }

  private def processEvents() {
    schedulerState.onBatchStart(this)

    // Precondition: there is at least one pending event.
    // Return value:
    // - `false` iff stopped by preemption
    // - `true` iff stopped because there are no events
    @tailrec def drain(c: Connector[_]): Boolean = {
      val remaining = c.dequeue()
      if (schedulerState.onBatchEvent(this)) {
        // Need to consume some more.
        if (remaining > 0 && !c.localChannel.isSealed) {
          drain(c)
        } else {
          val nc = popNextPending()
          if (nc != null) drain(nc)
          else true
        }
      } else {
        // Done consuming -- see if the connector needs to be enqueued.
        if (remaining > 0 && !c.localChannel.isSealed) monitor.synchronized {
          pendingQueues.enqueue(c)
        }
        false
      }
    }

    var nc = popNextPending()
    var j = 0
    while (nc != null) {
      j += 1
      if (drain(nc)) {
        nc = null
        spins = spinSpeculation * spinFactor
        while (spins > 0) {
          spins -= 1
          if (spins % spinFactor == 0) {
            nc = popNextPending()
          }
          if (nc != null) spins = 0
        }
      } else {
        nc = null
      }
    }

    val samplingProbability = randomDouble()
    if (samplingProbability < samplingFrequency) {
      spins = 0
      samplingFrequency = math.max(minSamplingFrequency, samplingFrequency - 0.02)
      val maxSpins = histogramSize * spinFactor
      while (spins < maxSpins) {
        if (spins % spinFactor == 0) {
          nc = popNextPending()
        }
        if (nc != null) {
          val fDiff = 0.06 * (maxSpins - spins) / maxSpins
          samplingFrequency = math.min(maxSamplingFrequency, samplingFrequency + fDiff)
          if (histogram == null) histogram = new Array(histogramSize)
          while (spins < histogramSize * spinFactor) {
            histogram(spins / spinFactor) += 1
            spins += spinFactor
          }
          drain(nc)
        }
        spins += 1
      }
      sampleCount += 1
      if (sampleCount == sampleSize) {
        sampleCount = 0
        samplingFrequency = math.max(minSamplingFrequency, samplingFrequency - 0.02)
        var i = 0
        var bestdiff = 0.0
        var besti = 0
        while (i < histogramSize && histogram != null) {
          val p = 1.0 * histogram(i) / sampleSize
          val d = 1.0 * i / histogramSize
          val cur = 1.0 * d - p
          if (cur < bestdiff) {
            bestdiff = cur
            besti = i
          }
          histogram(i) = 0
          i += 1
        }
        spinSpeculation = besti
        // if (histogram != null) {
        //   println(sampleCount + ": " + spinSpeculation +
        //     ", freq = " + samplingFrequency +
        //     ", hist = " + histogram.mkString(", "))
        //   i = 0
        //   while (i < histogramSize) {
        //     histogram(i) = 0
        //     i += 1
        //   }
        // }
      }
      if (randomDouble() < profileUpdateProbability) {
        Frame.updateSamplingFrequencyProfile(reactor.getClass, samplingFrequency)
      }
    }
    scheduleCount += 1
  }

  private def spinFactor: Int = 128

  private def sampleSize: Int = 40

  private def histogramSize: Int = 32

  private def maxSamplingFrequency: Double = 0.15

  private def minSamplingFrequency: Double = 0.001

  private def globalInitialSamplingFrequency = 0.002

  private def profileUpdateProbability: Double = 0.1

  private def computeInitialSamplingFrequency(): Double = {
    if (reactorSystem.bundle.schedulerConfig.speculativeLagging == 0) -1.0
    else {
      val profile = Frame.profiles.get(reactor.getClass)
      if (profile == null) globalInitialSamplingFrequency
      else profile.samplingFrequency
    }
  }

  private def randomBits(bits: Int): Int = {
    seed = (seed * 0x5DEECE66DL + 0xBL) & ((1L << 48) - 1);
    (seed >>> (48 - bits)).toInt
  }

  private def randomDouble(): Double = {
    val hi = randomBits(26)
    val lo = randomBits(27)
    val num = (hi.toLong << 27) + lo
    val den = (1L << 53).toDouble
    num / den
  }

  private def checkTerminated(forcedTermination: Boolean) {
    var emitTerminated = false
    monitor.synchronized {
      if (lifecycleState == Frame.Running) {
        if (forcedTermination || (pendingQueues.isEmpty && nonDaemonCount == 0)) {
          lifecycleState = Frame.Terminated
          emitTerminated = true
        }
      }
    }
    if (emitTerminated) {
      try {
        reactorSystem.debugApi.reactorTerminated(reactor)
        if (reactor != null) sysEmitter.react(ReactorTerminated)
      } finally {
        var done = false
        while (!done) {
          val info = reactorSystem.frames.forName(name)
          if (info == null) {
            // This should not happen, since the frame is at all times isolated.
            // Reaching this point means that there is some other code that corrupts
            // the `frames` map, or that a scheduler schedule the frame in the
            // `initSchedule` method, which it is not allowed to do.
            throw new IllegalStateException("Frame removed before termination.")
          } else {
            val ninfo = info.retainOnlyListeners
            done = {
              if (ninfo != null) reactorSystem.frames.tryReplace(name, info, ninfo)
              else reactorSystem.frames.tryRelease(name)
            }
          }
        }
      }
    }
  }

  private def processBatch() {
    checkFresh()
    try {
      sysEmitter.react(ReactorScheduled)
      processEvents()
      sysEmitter.react(ReactorPreempted)
    } finally {
      checkTerminated(false)
    }
  }

  private def connectorName(conn: Connector[_]): String =
    this.name + "#" + conn.sharedChannel.url.anchor

  def hasTerminated: Boolean = monitor.synchronized {
    lifecycleState == Frame.Terminated
  }

  def hasPendingEvents: Boolean = monitor.synchronized {
    pendingQueues.nonEmpty
  }

  def estimateTotalPendingEvents: Int = monitor.synchronized {
    var count = 0
    for (c <- pendingQueues) count += c.queue.size
    count
  }

  def sealConnector(connector: Connector[_]): Unit = {
    monitor.synchronized {
      connector.localChannel.isOpen = false
      if (!connector.isDaemon) nonDaemonCount -= 1

      // Try to remove the connector.
      var done = false
      while (!done) {
        val info = reactorSystem.frames.forName(name)
        val ninfo = Frame.Info(this, info.connectors - connector.name)
        done = reactorSystem.frames.tryReplace(name, info, ninfo)
      }
    }
    assert(Reactor.selfAsOrNull != null)
    connector.queue.unreact()
  }

}


object Frame {
  private[reactors] sealed trait LifecycleState

  private[reactors] case object Fresh extends LifecycleState

  private[reactors] case object Running extends LifecycleState

  private[reactors] case object Terminated extends LifecycleState

  private[reactors] case class Info(
    frame: Frame, connectors: immutable.Map[String, AnyRef]
  ) extends Identifiable {
    def uid: Long = if (frame != null) frame.uid else -1
    def isEmpty: Boolean = frame == null
    def retainOnlyListeners: Info = {
      val listeners = connectors.collect {
        case (k, v: List[_]) => (k, v)
      }
      if (listeners.nonEmpty) Info(null, listeners)
      else null
    }
  }

  private[reactors] class Profile(
    val clazz: Class[_],
    @volatile private var rawSamplingFrequency: Double
  ) {
    def samplingFrequency: Double = rawSamplingFrequency

    def updateSamplingFrequency(f: Double): Unit = this.synchronized {
      rawSamplingFrequency = 0.8 * rawSamplingFrequency + 0.2 * f
    }
  }

  private[reactors] val profiles = new ConcurrentHashMap[Class[_], Profile]

  @tailrec
  private[reactors] def updateSamplingFrequencyProfile(c: Class[_], f: Double): Unit = {
    val profile = profiles.get(c)
    if (profile != null) profile.updateSamplingFrequency(f)
    else {
      profiles.putIfAbsent(c, new Profile(c, f))
      updateSamplingFrequencyProfile(c, f)
    }
  }
}
