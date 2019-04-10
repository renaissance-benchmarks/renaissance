/* scala-stm - (c) 2009-2012, Stanford University, PPL */

package scala.concurrent.stm.ccstm

import annotation.tailrec
import java.util.concurrent.TimeUnit

/** A retry set representation. */
private[ccstm] class RetrySet(val size: Int,
                              handles: Array[Handle[_]],
                              versions: Array[CCSTM.Version]) {
  import CCSTM._

  /** Returns the number of nanoseconds of blocking that was performed. */
  @throws(classOf[InterruptedException])
  def awaitRetry(timeoutNanos: Long): Long = {
    if (size == 0 && timeoutNanos == Long.MaxValue)
      throw new IllegalStateException("explicit retries cannot succeed because cumulative read set is empty")

    val begin = System.nanoTime

    val d = begin + timeoutNanos
    val deadline = if (d < 0) Long.MaxValue else d // handle arithmetic overflow

    val timeoutExceeded = !attemptAwait(deadline)

    val actualElapsed = System.nanoTime - begin

    if (Stats.top != null) {
      Stats.top.retrySet += size
      val millis = TimeUnit.NANOSECONDS.toMillis(actualElapsed)
      Stats.top.retryWaitElapsed += millis.asInstanceOf[Int]
    }

    // to cause the proper retryFor to wake up we need to present an illusion
    // that we didn't block for too long
    //
    //  reportedElapsed = min(now, deadline) - begin
    //  reportedElapsed = min(now - begin, deadline - begin)
    math.min(actualElapsed, deadline - begin)
  }

  /** Returns true if something changed, false if the deadline was reached. */
  @throws(classOf[InterruptedException])
  private def attemptAwait(nanoDeadline: Long): Boolean = {
    // Spin a few times, counting one spin per read set element
    var spins = 0
    while (size > 0 && spins < SpinCount + YieldCount) {
      if (changed)
        return true
      spins += size
      if (spins > SpinCount) {
        Thread.`yield`
        if (nanoDeadline != Long.MaxValue && System.nanoTime > nanoDeadline)
          return false
      }
    }

    return blockingAttemptAwait(nanoDeadline)
  }

  @throws(classOf[InterruptedException])
  @tailrec
  private def blockingAttemptAwait(nanoDeadline: Long,
                                   event: WakeupManager.Event = wakeupManager.subscribe,
                                   i: Int = size - 1): Boolean = {
    if (i < 0) {
      // event has been completed, time to block
      if (!event.tryAwaitUntil(nanoDeadline))
        false // timed out
      else
        changed || blockingAttemptAwait(nanoDeadline) // event fired
    } else {
      // still building the event
      val h = handles(i)
      if (!event.addSource(h))
        changed || blockingAttemptAwait(nanoDeadline) // event fired
      else if (!addPendingWakeup(h, versions(i)))
        true // direct evidence of change
      else
        blockingAttemptAwait(nanoDeadline, event, i - 1) // keep building
    }
  }

  @tailrec
  private def addPendingWakeup(handle: Handle[_], ver: CCSTM.Version): Boolean = {
    val m = handle.meta
    if (changing(m) || version(m) != ver)
      false // handle has already changed
    else if (pendingWakeups(m) || handle.metaCAS(m, withPendingWakeups(m)))
      true // already has pending wakeup, or CAS to add it was successful
    else
      addPendingWakeup(handle, ver) // try again
  }

  private def changed: Boolean = {
    var i = size - 1
    while (i >= 0) {
      val m = handles(i).meta
      if (changing(m) || version(m) != versions(i))
        return true
      i -= 1
    }
    return false
  }

}
