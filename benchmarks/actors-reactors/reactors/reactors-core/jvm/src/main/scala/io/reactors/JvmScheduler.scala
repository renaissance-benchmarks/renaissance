package io.reactors



import io.reactors.common.freshId
import io.reactors.concurrent._
import java.util.concurrent._
import java.util.concurrent.atomic.AtomicReference
import java.util.TimerTask
import scala.annotation.tailrec
import scala.collection._
import scala.concurrent.ExecutionContext



object JvmScheduler {
  /** Scheduler that shares the global Scala execution context.
   */
  lazy val globalExecutionContext: Scheduler =
    Executed.from(ExecutionContext.Implicits.global)

  private[reactors] class ReactorForkJoinReanimatorThread(
    val pool: ReactorForkJoinPool
  ) extends Thread {
    val reanimatorPeriod = 200

    setName("reactors-io-scheduler-reanimator")
    setDaemon(true)

    private def reanimate() {
      val it = pool.workers.elements()
      while (it.hasMoreElements) {
        val worker = it.nextElement()
        val pendingFrame = worker.miniQueue.get
        if (pendingFrame != null) {
          if (worker.miniQueue.compareAndSet(pendingFrame, null)) {
            val r = pendingFrame.schedulerState.asInstanceOf[Runnable]
            pool.execute(r)
          }
        }
      }
    }

    @tailrec
    override final def run() {
      try {
        reanimate()
      } catch {
        case t: Throwable =>
          // Invoke handler and ignore failures.
          try pool.getUncaughtExceptionHandler.uncaughtException(this, t)
          finally {}
      } finally {}
      Thread.sleep(reanimatorPeriod)
      run()
    }
  }

  private[reactors] class ReactorForkJoinWorkerThread(
    val reactorPool: ReactorForkJoinPool
  ) extends ForkJoinWorkerThread(reactorPool) with Reactor.ReactorThread {
    import ReactorForkJoinWorkerThread._
    val miniQueue = new AtomicReference[Frame](null)
    private var state: AnyRef = ASLEEP

    setName(s"reactors-io-scheduler-${getName}")

    override def onStart() {
      super.onStart()
      reactorPool.workers.put(getId, this)
    }

    override def onTermination(t: Throwable) {
      reactorPool.workers.remove(getId)
      super.onTermination(t)
    }

    // Optimized version - postpone task creation and try to take over.
    @tailrec
    final def execute(frame: Frame) {
      val state = miniQueue.get
      if (state eq null) {
        if (!miniQueue.compareAndSet(state, frame)) execute(frame)
      } else {
        if (!miniQueue.compareAndSet(state, null)) execute(frame)
        else {
          val r = state.schedulerState.asInstanceOf[Runnable]
          ForkJoinTask.adapt(r).fork()
          execute(frame)
        }
      }
    }

    // // Non-optimized version.
    // final def execute(frame: Frame) {
    //   val r = frame.schedulerState.asInstanceOf[Runnable]
    //   ForkJoinTask.adapt(r).fork()
    // }

    private def pollPool(fj: ReactorForkJoinPool): Boolean = {
      val task = fj.poll()
      if (task != null) {
        task.invoke()
        true
      } else false
    }

    @tailrec
    private def popMiniQueue(): Frame = {
      val state = miniQueue.get
      if (state != null) {
        if (!miniQueue.compareAndSet(state, null)) popMiniQueue()
        else state
      } else null
    }

    private def executeLater(frame: Frame) {
      if (frame != null) {
        val r = frame.schedulerState.asInstanceOf[Runnable]
        ForkJoinTask.adapt(r).fork()
      }
    }

    private def executeNow(frame: Frame): Boolean = {
      if (frame != null) {
        frame.executeBatch()
        true
      } else false
    }

    def preschedule() {
      if (state != POSTSCHEDULING) state = AWAKE
    }

    def postschedule(system: ReactorSystem, t: Throwable) {
      if (state == POSTSCHEDULING) return
      if (t != null) {
        state = ASLEEP
        executeLater(popMiniQueue())
        return
      } else {
        state = POSTSCHEDULING
      }

      try {
        getPool match {
          case fj: ReactorForkJoinPool =>
            var loopsLeft = system.bundle.schedulerConfig.postscheduleCount
            while (loopsLeft > 0) {
              var executedSomething = pollPool(fj)
              executedSomething ||= executeNow(popMiniQueue())
              if (executedSomething) {
                loopsLeft -= 1
              } else {
                loopsLeft = 0
              }
            }
          case _ =>
        }
      } finally {
        state = ASLEEP
        executeLater(popMiniQueue())
      }
    }
  }

  private[reactors] object ReactorForkJoinWorkerThread {
    val ASLEEP = new AnyRef {}
    val AWAKE = new AnyRef {}
    val POSTSCHEDULING = new AnyRef {}
  }

  private[reactors] class ReactorForkJoinPool extends ForkJoinPool(
    Runtime.getRuntime.availableProcessors,
    new ForkJoinPool.ForkJoinWorkerThreadFactory {
      def newThread(pool: ForkJoinPool) =
        new ReactorForkJoinWorkerThread(pool.asInstanceOf[ReactorForkJoinPool])
    },
    null,
    false
  ) {
    private[reactors] val reanimator =
      new ReactorForkJoinReanimatorThread(this)
    private[reactors] val workers =
      new ConcurrentHashMap[Long, ReactorForkJoinWorkerThread]

    reanimator.start()

    def poll() = pollSubmission()
  }

  /** Default fork/join pool instance used by the default scheduler.
   */
  lazy val defaultForkJoinPool: ForkJoinPool = new ReactorForkJoinPool

  /** Default reactor scheduler.
   */
  lazy val default: Scheduler = new Executed(defaultForkJoinPool)

  /** A scheduler that always starts a reactor on a dedicated thread.
   */
  lazy val newThread: Scheduler = new Dedicated.NewThread(true)

  /** A scheduler that reuses (piggybacks) the current thread to run the reactor.
   *
   *  Until the reactor terminates, the current thread is blocked and cannot be used any
   *  more.
   *  This scheduler cannot be used to start reactors from within another reactor,
   *  and is typically used to turn the application main thread into a reactor.
   *
   *  @see [[org.reactors.JvmScheduler.Dedicated.Piggyback]]
   */
  lazy val piggyback: Scheduler = new Dedicated.Piggyback()

  /** A `Scheduler` that reuses the target Java `Executor`.
   *
   *  It checks if the specified executor is a `ForkJoinPool` that uses
   *  `ReactorForkJoinWorkerThread` and, if so, applies additional optimizations:
   *
   *  - If `schedule` is called from a `ForkJoinWorkerThread` that belongs to the
   *    `ForkJoinPool` that is the `executor`, then a more lightweight mechanism is
   *    used to schedule the task.
   *  - When a frame completes execution, it calls `postschedule`. This will attempt to
   *    remove submitted tasks from the `ForkJoinPool` a certain of times and execute
   *    them directly. The `scheduler.default.postschedule-count` bundle configuration
   *    key is the maximum number of attempts.  If removing is not successful,
   *    this immediately stops.
   *  - Each `ReactorForkJoinWorkerThread` has an associated mini-queue into which it
   *    stores at most one scheduled `Frame`. Any frame must first be placed onto the
   *    mini-queue before getting converted into a task and sent to the queue. Before
   *    any such worker thread returns control to the pool, it must flush its
   *    mini-queue. Simultaneously, there is a reanimator thread that periodically
   *    traverses the mini-queues of all the threads, and flushes them if necessary.
   *
   *  @param executor       The `Executor` used to schedule reactor tasks.
   */
  class Executed(
    val executor: java.util.concurrent.Executor
  ) extends Scheduler {
    def schedule(frame: Frame): Unit = {
      Thread.currentThread match {
        case t: ReactorForkJoinWorkerThread if t.getPool eq executor =>
          t.execute(frame)
        case t: ForkJoinWorkerThread if t.getPool eq executor =>
          val r = frame.schedulerState.asInstanceOf[Runnable]
          ForkJoinTask.adapt(r).fork()
        case _ =>
          executor.execute(frame.schedulerState.asInstanceOf[Runnable])
      }
    }

    override def newState(frame: Frame): Scheduler.State = {
      new Scheduler.State.Default with Runnable {
        def run() = {
          try frame.executeBatch()
          catch frame.reactorSystem.errorHandler
        }
      }
    }

    override def preschedule(system: ReactorSystem) {
      Thread.currentThread match {
        case t: ReactorForkJoinWorkerThread =>
          t.preschedule()
        case _ =>
          return
      }
    }

    override def postschedule(system: ReactorSystem, throwable: Throwable) {
      Thread.currentThread match {
        case t: ReactorForkJoinWorkerThread =>
          t.postschedule(system, throwable)
        case _ =>
          return
      }
    }
  }

  object Executed {
    def from(ec: ExecutionContext): Executed = {
      val executor = new Executor {
        override def execute(r: Runnable): Unit = ec.execute(r)
      }
      new Executed(executor)
    }
  }

  /** An abstract scheduler that always dedicates a thread to a reactor.
   */
  abstract class Dedicated extends Scheduler {
    def schedule(frame: Frame): Unit = {
      frame.schedulerState.asInstanceOf[Dedicated.Worker].awake()
    }
  }

  /** Contains utility classes and implementations of the dedicated scheduler.
   */
  object Dedicated {

    private[reactors] class Worker(val frame: Frame)
    extends Scheduler.State.Default {
      @volatile var thread: Thread = _

      @tailrec final def loop(): Unit = {
        val handler = frame.reactorSystem.errorHandler
        try {
          frame.executeBatch()
          frame.monitor.synchronized {
            while (!frame.hasTerminated && !frame.hasPendingEvents) {
              frame.monitor.wait()
            }
          }
        } catch {
          case t if handler.isDefinedAt(t) =>
            handler(t)
            throw t
        }
        if (!frame.hasTerminated) loop()
      }

      def awake() {
        frame.monitor.synchronized {
          frame.monitor.notify()
        }
      }
    }

    private[reactors] class WorkerThread(val worker: Worker) extends Thread {
      override def run() = worker.loop()
    }

    /** Starts a new dedicated thread for each reactor that is created.
     *
     *  The new thread does not stop until the reactor terminates.
     *  The thread is optionally a daemon thread.
     *
     *  @param isDaemon          Is the new thread a daemon.
     */
    class NewThread(
      val isDaemon: Boolean
    ) extends Dedicated {
      override def newState(frame: Frame): Dedicated.Worker = {
        val w = new Worker(frame)
        w.thread = new WorkerThread(w)
        w
      }

      override def schedule(frame: Frame): Unit = {
        val t = frame.schedulerState.asInstanceOf[Worker].thread
        if (t.getState == Thread.State.NEW) t.start()
        super.schedule(frame)
      }
    }

    /** Executes the reactor on the thread that called the reactor system's `spawn`
     *  method to create the reactor.
     *
     *  While reactors are generally sent off to some other thread or computer for
     *  execution after the reactor has been created, this scheduler executes the
     *  reactor on the current thread.
     *
     *  The current thread is permanently blocked until the reactor terminates.
     *  Using this scheduler from an existing reactor is illegal and throws an
     *  exception.
     *  This scheduler is meant to be used to turn the application main thread
     *  into a reactor, i.e. to step from the normal multithreaded world into
     *  the reactor universe.
     */
    class Piggyback
    extends Dedicated {
      override def newState(frame: Frame): Dedicated.Worker = {
        val w = new Worker(frame)
        w
      }

      override def initSchedule(frame: Frame) {
        super.initSchedule(frame)
        val current: Reactor[_] = Reactor.selfAsOrNull
        if (current != null) throw new IllegalStateException(
          s"Cannot use piggyback scheduler from within a reactor $current.")
      }

      override def schedule(frame: Frame) {
        frame.schedulerState match {
          case w: Worker =>
            if (w.thread == null) {
              w.thread = Thread.currentThread
              w.loop()
            } else {
              super.schedule(frame)
            }
        }
      }
    }

  }

  /** Executes the reactor on the timer thread.
   *
   *  The reactor is run every `period` milliseconds.
   *  This is regardless of the number of events in this reactor's event queue.
   *
   *  When the reactor runs, it flushes as many events as there are initially pending
   *  events.
   *
   *  @param period       Period between executing the reactor.
   *  @param isDaemon     Is the timer thread a daemon thread.
   */
  class Timer(
    private val period: Long,
    val isDaemon: Boolean = true
  ) extends Scheduler {
    private var timer: java.util.Timer = null
    private val frames = mutable.Set[Frame]()

    def shutdown() = if (timer != null) timer.cancel()

    override def newState(frame: Frame) = new Timer.State

    def schedule(frame: Frame) {
      val state = frame.schedulerState.asInstanceOf[Timer.State]
      if (state.task == null) state.synchronized {
        if (state.task == null) {
          state.task = new TimerTask {
            timerTask =>
            def run() {
              try {
                if (frame.hasTerminated) {
                  timerTask.cancel()
                  removeFrame(frame)
                } else {
                  frame.executeBatch()
                  frame.activate(false)
                }
              } catch frame.reactorSystem.errorHandler
            }
          }
          timer.schedule(state.task, period, period)
        }
      }
    }

    override def initSchedule(frame: Frame) {
      super.initSchedule(frame)
      addFrame(frame)
    }

    private def addFrame(frame: Frame) = frames.synchronized {
      frames += frame
      if (frames.size == 1) {
        timer = new java.util.Timer(s"Scheduler-${freshId[Timer]}", isDaemon)
      }
    }

    private def removeFrame(frame: Frame) = frames.synchronized {
      frames -= frame
      if (frames.size == 0) {
        timer.cancel()
        timer = null
      }
    }
  }

  object Timer {
    /** Holds state of frames scheduled by the `Timer` scheduler.
     */
    class State extends Scheduler.State.Default {
      @volatile var task: TimerTask = null

      override def onBatchStart(frame: Frame): Unit = {
        allowedBudget = frame.estimateTotalPendingEvents
      }
    }
  }

  object Key {
    val globalExecutionContext = "org.reactors.JvmScheduler::globalExecutionContext"
    val default = "org.reactors.JvmScheduler::default"
    val newThread = "org.reactors.JvmScheduler::newThread"
    val piggyback = "org.reactors.JvmScheduler::piggyback"
    def defaultScheduler = default
  }

  private[reactors] val javaKey = Key
}
