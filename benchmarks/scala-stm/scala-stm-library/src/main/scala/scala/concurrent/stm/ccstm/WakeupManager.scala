/* scala-stm - (c) 2009-2012, Stanford University, PPL */

package scala.concurrent.stm.ccstm


import java.util.concurrent.atomic.{AtomicReferenceArray, AtomicLongArray}
import java.util.concurrent.locks.AbstractQueuedSynchronizer
import java.lang.reflect.{InvocationTargetException, Method}

object WakeupManager {
  trait Event {
    def triggered: Boolean

    /** Returns false if triggered. */
    def addSource(handle: Handle[_]): Boolean

    @throws(classOf[InterruptedException])
    def await()

    /** Use a nanoDeadline of `Long.MaxValue` to wait forever. */
    @throws(classOf[InterruptedException])
    def tryAwaitUntil(nanoDeadline: Long): Boolean
  }

  // TODO: remove WakeupManager.blocking once we no longer compile for 2.9
  // This is a hack so that we can use the new scala.concurrent.BlockContext
  // (available in Scala >= 2.10) while still compiling for 2.9.  Although
  // there is a bit of overhead, we are careful to only pay it when we are
  // actually about to park the thread (which is quite expensive on its own).

  val blockingMethod: Method = {
    try {
      Class.forName("scala.concurrent.package").getMethod("blocking", classOf[Function0[_]])
    } catch {
      case _: ClassNotFoundException => null
      case _: NoSuchMethodException => null
    }
  }

  /** Returns `body()`, cooperating with 2.10's fork-join system. */
  def blocking[A](body: => A): A = {
    if (blockingMethod != null) {
      try {
        blockingMethod.invoke(null, (body _).asInstanceOf[Function0[_]]).asInstanceOf[A]
      } catch {
        case x: InvocationTargetException => throw x.getTargetException
      }
    } else {
      body
    }
  }
}

/** Provides a service that extends the paradigm of wait+notifyAll to allow
 *  bulk wait and bulk notification; also does not require that the waiter and
 *  the notifier share an object reference.  There is a chance of a false
 *  positive.
 *
 *@author Nathan Bronson
 */
private[ccstm] final class WakeupManager(numChannels: Int, numSources: Int) {
  import CCSTM.hash
  import WakeupManager.blocking

  def this() = this(64, 512)

  assert(numChannels > 0 && numChannels <= 64 && (numChannels & (numChannels - 1)) == 0)
  assert(numSources > 0 && (numSources & (numSources - 1)) == 0)

  // To reduce false sharing.  Assume 64 byte cache lines and 4 byte pointers.
  private final val ChannelSpacing = 16

  private val pending = new AtomicLongArray(numSources)
  private val events = new AtomicReferenceArray[EventImpl](numChannels * ChannelSpacing)
  
  /** The returned value must later be passed to `trigger`.
   *  Multiple return values may be passed to a single invocation of
   *  `trigger` by merging them with bitwise-OR.
   */
  def prepareToTrigger(handle: Handle[_]): Long = {
    val i = hash(handle.base, handle.metaOffset) & (numSources - 1)
    var z = 0L
    do {
      z = pending.get(i)
    } while (z != 0L && !pending.compareAndSet(i, z, 0L))
    z
  }

  /** Completes the wakeups started by `prepareToTrigger`.  If a
   *  thread completes `e = subscribe; e.addSource(r,o)` prior to
   *  a call to `prepareToTrigger(r,o)` call whose return value is
   *  included in `wakeups`, then any pending call to
   *  `e.await` will return now and any future calls will return
   *  immediately.
   */
  def trigger(wakeups: Long) {
    var channel = 0
    var w = wakeups
    while (w != 0) {
      val s = java.lang.Long.numberOfTrailingZeros(w)
      w >>>= s
      channel += s
      trigger(channel)
      w >>>= 1
      channel += 1
    }
  }

  private def trigger(channel: Int) {
    val i = channel * ChannelSpacing
    val e = events.get(i)
    if (e != null) {
      e.trigger()
      events.compareAndSet(i, e, null)
    }
  }

  /** See `trigger`. */
  def subscribe: WakeupManager.Event = {
    // Picking the waiter's identity using the thread hash means that there is
    // a possibility that we will get repeated interference with another thread
    // in a per-program-run way, but it minimizes saturation of the pending
    // wakeups, which is quite important.
    subscribe(hash(Thread.currentThread) & (numChannels - 1))
  }

  private def subscribe(channel: Int): EventImpl = {
    val i = channel * ChannelSpacing
    (while (true) {
      val existing = events.get(i)
      if (existing != null && !existing.triggered)
        return existing
      val fresh = new EventImpl(channel)
      if (events.compareAndSet(i, existing, fresh))
        return fresh
    }).asInstanceOf[Nothing]
  }

  class EventImpl(channel: Int) extends AbstractQueuedSynchronizer() with WakeupManager.Event {
    private val mask = 1L << channel

    setState(1)

    //// adapted from CountDown.Sync

    override def tryAcquireShared(acquires: Int): Int = if (getState == 0) 1 else -1

    override def tryReleaseShared(releases: Int): Boolean = getState == 1 && compareAndSetState(1, 0)

    //// Event

    def triggered = getState == 0

    /** Returns false if triggered. */
    def addSource(handle: Handle[_]): Boolean = {
      if (triggered) {
        false
      } else {
        val i = hash(handle.base, handle.metaOffset) & (numSources - 1)
        var p = pending.get(i)
        while((p & mask) == 0 && !pending.compareAndSet(i, p, p | mask)) {
          if (triggered)
            return false
          p = pending.get(i)
        }
        true
      }
    }

    @throws(classOf[InterruptedException])
    def await() {
      val f = tryAwaitUntil(Long.MaxValue)
      assert(f)
    }

    @throws(classOf[InterruptedException])
    def tryAwaitUntil(nanoDeadline: Long): Boolean = {
      if (triggered) {
        true
      } else if (nanoDeadline == Long.MaxValue) {
        blocking { acquireSharedInterruptibly(1) }
        true
      } else {
        val remaining = nanoDeadline - System.nanoTime
        remaining > 0 && blocking { tryAcquireSharedNanos(1, remaining) }
      }
    }

    private[WakeupManager] def trigger() { releaseShared(1) }
  }
}
