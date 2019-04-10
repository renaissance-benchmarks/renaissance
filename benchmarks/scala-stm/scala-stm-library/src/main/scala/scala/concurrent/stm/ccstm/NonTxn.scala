/* scala-stm - (c) 2009-2012, Stanford University, PPL */

package scala.concurrent.stm
package ccstm

import annotation.tailrec


/** The object that contains the code for non-transactional read and write
 *  barriers.
 *
 *  @author Nathan Bronson
 */
private[ccstm] object NonTxn {
  import CCSTM._

  //////////////// lock waiting

  @throws(classOf[InterruptedException])
  private def weakAwaitUnowned(handle: Handle[_], m0: Meta) {
    CCSTM.weakAwaitUnowned(handle, m0, null)
  }

  //////////////// value waiting

  @throws(classOf[InterruptedException])
  private def weakAwaitNewVersion(handle: Handle[_], m0: Meta) {
    // spin a bit
    var m = 0L
    var spins = 0
    do {
      val m = handle.meta
      if (version(m) != version(m0))
        return

      spins += 1
      if (spins > SpinCount)
        Thread.`yield`
    } while (spins < SpinCount + YieldCount)

    weakNoSpinAwaitNewVersion(handle, m)
  }

  @throws(classOf[InterruptedException])
  private def weakNoSpinAwaitNewVersion(handle: Handle[_], m0: Meta) {
    val event = wakeupManager.subscribe
    event.addSource(handle)
    do {
      val m = handle.meta
      if (version(m) != version(m0) || changing(m)) {
        // observed new version, or likely new version (after unlock)
        return
      }

      // not changing, so okay to set PW bit
      if (pendingWakeups(m) || handle.metaCAS(m, withPendingWakeups(m))) {
        // after the block, things will have changed with reasonably high
        // likelihood (spurious wakeups are okay)
        event.await
        return
      }
    } while (!event.triggered)
  }

  //////////////// value waiting with timeout

  @throws(classOf[InterruptedException])
  private def weakAwaitNewVersion(handle: Handle[_], m0: Meta, nanoDeadline: Long): Boolean = {
    // spin a bit
    var m = 0L
    var spins = 0
    do {
      val m = handle.meta
      if (version(m) != version(m0))
        return true

      spins += 1
      if (spins > SpinCount) {
        if (System.nanoTime >= nanoDeadline)
          return false
        Thread.`yield`
      }
    } while (spins < SpinCount + YieldCount)

    if (changing(m)) {
      // ignore deadline for this, it should be fast
      weakAwaitUnowned(handle, m)
      return true
    } else {
      return weakNoSpinAwaitNewVersion(handle, m, nanoDeadline)
    }
  }

  @throws(classOf[InterruptedException])
  private def weakNoSpinAwaitNewVersion(handle: Handle[_], m0: Meta, nanoDeadline: Long): Boolean = {
    val event = wakeupManager.subscribe
    event.addSource(handle)
    do {
      val m = handle.meta
      if (version(m) != version(m0) || changing(m)) {
        // observed new version, or likely new version (after unlock)
        return true
      }

      // not changing, so okay to set PW bit
      if (pendingWakeups(m) || handle.metaCAS(m, withPendingWakeups(m))) {
        // after the block, things will have changed with reasonably high
        // likelihood (spurious wakeups are okay)
        return event.tryAwaitUntil(nanoDeadline)
      }
    } while (!event.triggered)
    return true
  }

  //////////////// lock acquisition

  @throws(classOf[InterruptedException])
  private def acquireLock(handle: Handle[_], exclusive: Boolean): Meta = {
    var m0 = 0L
    var m1 = 0L
    do {
      m0 = handle.meta
      while (owner(m0) != unownedSlot) {
        weakAwaitUnowned(handle, m0)
        m0 = handle.meta
      }
      val mOwned = withOwner(m0, nonTxnSlot)
      m1 = if (exclusive) withChanging(mOwned) else mOwned
    } while (!handle.metaCAS(m0, m1))
    m1
  }

  /** Returns 0L on failure. */
  private def tryAcquireExclusiveLock(handle: Handle[_]): Meta = {
    val m0 = handle.meta
    if (owner(m0) != unownedSlot) return 0L

    val m1 = withChanging(withOwner(m0, nonTxnSlot))

    if (!handle.metaCAS(m0, m1)) return 0L

    return m1
  }

  private def upgradeLock(handle: Handle[_], m0: Meta): Meta = {
    var before = m0
    if (!handle.metaCAS(before, withChanging(before))) {
      // must have been a concurrent set of pendingWakeups
      before = withPendingWakeups(before)
      handle.meta = withChanging(before)
    }
    withChanging(before)
  }

  private def commitUpdate[T](handle: Handle[T], m0: Meta, newData: T) {
    val newVersion = CCSTM.nonTxnWriteVersion(version(m0))
    handle.data = newData
    releaseLock(handle, m0, newVersion)
  }

  private def discardLock(handle: Handle[_], m0: Meta) {
    releaseLock(handle, m0, version(m0))
  }

  private def releaseLock(handle: Handle[_], m0: Meta, newVersion: Version) {
    handle.meta = withCommit(m0, newVersion)

    if (pendingWakeups(m0))
      triggerWakeups(handle)
  }

  private def triggerWakeups(handle: Handle[_]) {
    wakeupManager.trigger(wakeupManager.prepareToTrigger(handle))
  }

  //////////////// public interface

  @throws(classOf[InterruptedException])
  def get[T](handle: Handle[T]): T = {
    var tries = 0
    var m0 = 0L
    while (tries < 100) {
      m0 = handle.meta
      if (changing(m0)) {
        weakAwaitUnowned(handle, m0)
      } else {
        val v = handle.data
        val m1 = handle.meta
        if (changingAndVersion(m0) == changingAndVersion(m1)) {
          return v
        }
      }
      tries += 1
    }
    return lockedGet(handle)
  }

  @throws(classOf[InterruptedException])
  private def lockedGet[T](handle: Handle[T]): T = {
    val m0 = acquireLock(handle, false)
    val z = handle.data
    discardLock(handle, m0)
    z
  }

  @throws(classOf[InterruptedException])
  def await[T](handle: Handle[T], pred: T => Boolean) {
    while (true) {
      val m0 = handle.meta
      if (changing(m0)) {
        weakAwaitUnowned(handle, m0)
      } else {
        val v = handle.data
        val m1 = handle.meta
        if (changingAndVersion(m0) == changingAndVersion(m1)) {
          // stable read of v
          if (pred(v)) {
            // success!
            return
          }

          // wait for a new version
          weakAwaitNewVersion(handle, m1)
        }
      }
    }
  }

  def tryAwait[T](handle: Handle[T], pred: T => Boolean, timeoutNanos: Long): Boolean = {
    var begin = 0L
    (while (true) {
      val m0 = handle.meta
      if (changing(m0)) {
        if (begin == 0L)
          begin = System.nanoTime
        weakAwaitUnowned(handle, m0)
      } else {
        val v = handle.data
        val m1 = handle.meta
        if (changingAndVersion(m0) == changingAndVersion(m1)) {
          // stable read of v
          if (pred(v))
            return true

          // no need for base time with zero timeout
          if (timeoutNanos <= 0)
            return false

          // wait for a new version
          if (begin == 0L)
            begin = System.nanoTime
          if (!weakAwaitNewVersion(handle, m1, begin + timeoutNanos))
            return false
        }
      }
    }).asInstanceOf[Nothing]
  }

  @throws(classOf[InterruptedException])
  def set[T](handle: Handle[T], v: T) {
    val m0 = acquireLock(handle, true)
    commitUpdate(handle, m0, v)
  }

  @throws(classOf[InterruptedException])
  def swap[T](handle: Handle[T], v: T): T = {
    val m0 = acquireLock(handle, true)
    val z = handle.data
    commitUpdate(handle, m0, v)
    z
  }

  def trySet[T](handle: Handle[T], v: T): Boolean = {
    val m0 = tryAcquireExclusiveLock(handle)
    if (m0 == 0L) {
      false
    } else {
      commitUpdate(handle, m0, v)
      true
    }
  }

  @throws(classOf[InterruptedException])
  def compareAndSet[T](handle: Handle[T], before: T, after: T): Boolean = {
    // Try to acquire ownership.  If we can get it easily then we hold the lock
    // while evaluating before == handle.data, otherwise we try to perform an
    // invisible read to determine if the CAS will succeed, only waiting for
    // the lock if the CAS might go ahead.
    val m0 = handle.meta
    if (owner(m0) != unownedSlot) {
      return invisibleCAS(handle, before, after)
    }
    val m1 = withOwner(m0, nonTxnSlot)
    if (!handle.metaCAS(m0, m1)) {
      return invisibleCAS(handle, before, after)
    }

    var success = false
    try {
      if (before == handle.data) {
        success = true
        val m2 = upgradeLock(handle, m1)
        commitUpdate(handle, m2, after)
      }
      success
    } finally {
      if (!success)
        discardLock(handle, m1)
    }
  }

  @throws(classOf[InterruptedException])
  private def invisibleCAS[T](handle: Handle[T], before: T, after: T): Boolean = {
    // this is the code from get, inlined so that we have access to the version
    // number as well with no boxing
    var m0 = 0L
    var m1 = 0L
    var v: T = null.asInstanceOf[T]
    do {
      m0 = handle.meta
      while (changing(m0)) {
        weakAwaitUnowned(handle, m0)
        m0 = handle.meta
      }
      v = handle.data
      m1 = handle.meta
    } while (changingAndVersion(m0) != changingAndVersion(m1))

    // invisible failure?
    if (!(before == v)) return false

    // don't go directly to changing, because we can't run user code
    // (before.equals) there
    val m2 = acquireLock(handle, false)
    var success = false
    try {
      if (version(m2) == version(m1) || before == handle.data) {
        success = true
        val m3 = upgradeLock(handle, m2)
        commitUpdate(handle, m3, after)
      }
      success
    } finally {
      if (!success)
        discardLock(handle, m2)
    }
  }

  @throws(classOf[InterruptedException])
  def compareAndSetIdentity[T, R <: AnyRef with T](handle: Handle[T], before: R, after: T): Boolean = {
    // try to acquire exclusive ownership
    val m0 = handle.meta
    if (owner(m0) != unownedSlot) {
      return invisibleCASI(handle, before, after)
    }
    val m1 = withChanging(withOwner(m0, nonTxnSlot))
    if (!handle.metaCAS(m0, m1)) {
      return invisibleCASI(handle, before, after)
    }

    if (before eq handle.data.asInstanceOf[AnyRef]) {
      commitUpdate(handle, m1, after)
      true
    } else {
      discardLock(handle, m1)
      false
    }
  }

  @throws(classOf[InterruptedException])
  private def invisibleCASI[T, R <: T with AnyRef](handle: Handle[T], before: R, after: T): Boolean = {
    if (before eq get(handle).asInstanceOf[AnyRef]) {
      // CASI is different than CAS, because we don't have to invoke user code to
      // perform the comparison
      val m0 = acquireLock(handle, true)
      if (before eq handle.data.asInstanceOf[AnyRef]) {
        commitUpdate(handle, m0, after)
        true
      } else {
        discardLock(handle, m0)
        false
      }
    } else {
      // invisible failure
      false
    }
  }

  @throws(classOf[InterruptedException])
  def getAndTransform[T](handle: Handle[T], f: T => T): T = {
    getAndTransformImpl(handle, f, acquireLock(handle, false))
  }

  private def getAndTransformImpl[T](handle: Handle[T], f: T => T, m0: Meta): T = {
    val v0 = handle.data
    val repl = try { f(v0) } catch { case x: Throwable => discardLock(handle, m0) ; throw x }
    val m1 = upgradeLock(handle, m0)
    commitUpdate(handle, m1, repl)
    v0
  }

  @throws(classOf[InterruptedException])
  def transformAndGet[T](handle: Handle[T], f: T => T): T = {
    transformAndGetImpl(handle, f, acquireLock(handle, false))
  }

  private def transformAndGetImpl[T](handle: Handle[T], f: T => T, m0: Meta): T = {
    val repl = try { f(handle.data) } catch { case x: Throwable => discardLock(handle, m0) ; throw x }
    val m1 = upgradeLock(handle, m0)
    commitUpdate(handle, m1, repl)
    repl
  }

  @throws(classOf[InterruptedException])
  def transformAndExtract[T,V](handle: Handle[T], f: T => (T,V)): V = {
    val m0 = acquireLock(handle, false)
    val pair = try { f(handle.data) } catch { case x: Throwable => discardLock(handle, m0) ; throw x }
    val m1 = upgradeLock(handle, m0)
    commitUpdate(handle, m1, pair._1)
    pair._2
  }

  @throws(classOf[InterruptedException])
  def transformIfDefined[T](handle: Handle[T], pf: PartialFunction[T,T]): Boolean = {
    if (pf.isDefinedAt(get(handle))) {
      val m0 = acquireLock(handle, false)
      val v = handle.data
      if (try { pf.isDefinedAt(v) } catch { case x: Throwable => discardLock(handle, m0) ; throw x }) {
        val repl = try { pf(v) } catch { case x: Throwable => discardLock(handle, m0) ; throw x }
        val m1 = upgradeLock(handle, m0)
        commitUpdate(handle, m1, repl)
        true
      } else {
        discardLock(handle, m0)
        false
      }
    } else {
      // invisible failure
      false
    }
  }

  //////////////// multi-handle ops

  @throws(classOf[InterruptedException])
  def transform2[A, B, Z](handleA: Handle[A], handleB: Handle[B], f: (A, B) => (A, B, Z)): Z = {
    var mA0: Long = 0L
    var mB0: Long = 0L
    var tries = 0
    do {
      mA0 = acquireLock(handleA, true)
      mB0 = tryAcquireExclusiveLock(handleB)
      if (mB0 == 0) {
        // tryAcquire failed
        discardLock(handleA, mA0)
        mA0 = 0

        // did it fail because the handles are equal?
        if (handleA == handleB)
          return fallbackTransform2(handleA, handleB, f)

        // try it in the opposite direction
        mB0 = acquireLock(handleB, true)
        mA0 = tryAcquireExclusiveLock(handleA)

        if (mA0 == 0) {
          // tryAcquire failed
          discardLock(handleB, mB0)
          mB0 = 0

          tries += 1
          if (tries > 10)
            return fallbackTransform2(handleA, handleB, f)
        }
      }
    } while (mB0 == 0)

    val (a, b, z) = try {
      f(handleA.data, handleB.data)
    } catch {
      case x: Throwable => {
        discardLock(handleA, mA0)
        discardLock(handleB, mB0)
        throw x
      }
    }

    handleA.data = a
    handleB.data = b

    val wv = CCSTM.nonTxnWriteVersion(math.max(version(mA0), version(mB0)))
    releaseLock(handleA, mA0, wv)
    releaseLock(handleB, mB0, wv)
    return z
  }

  @throws(classOf[InterruptedException])
  private def fallbackTransform2[A, B, Z](handleA: Handle[A], handleB: Handle[B], f: (A, B) => (A, B, Z)): Z = {
    atomic { t =>
      val txn = t.asInstanceOf[InTxnImpl]
      val a0 = txn.get(handleA)
      val b0 = txn.get(handleB)
      val (a1, b1, z) = f(a0, b0)
      txn.set(handleA, a1)
      txn.set(handleB, b1)
      z
    }
  }

  @throws(classOf[InterruptedException])
  def ccasi[A <: AnyRef, B <: AnyRef](handleA: Handle[A], a0: A, handleB: Handle[B], b0: B, b1: B): Boolean = {
    var tries = 0
    while (tries < 10) {
      // acquire exclusive ownership of B, then decide
      val mB0 = acquireLock(handleB, true)
      if (b0 ne handleB.data.asInstanceOf[AnyRef]) {
        // b doesn't match
        discardLock(handleB, mB0)
        return false
      }

      var mA0 = handleA.meta
      while (!changing(mA0)) {
        // attempt a stable read of A
        val a = handleA.data
        val mA1 = handleA.meta
        if (changingAndVersion(mA0) != changingAndVersion(mA1)) {
          // read of A was unstable, but we don't need to block right now
          mA0 = mA1
        } else {
          // we can definitely complete the CCASI
          if (a eq a0) {
            // a0 and b0 both match
            commitUpdate(handleB, mB0, b1)
            return true
          } else {
            // a0 doesn't match
            discardLock(handleB, mB0)
            return false
          }
        }
      }

      // release our lock before waiting for A
      discardLock(handleB, mB0)
      weakAwaitUnowned(handleA, mA0)

      tries += 1
    }

    // fall back on a transaction
    return atomic { t =>
      val txn = t.asInstanceOf[InTxnImpl]
      (txn.get(handleA) eq a0) && (txn.get(handleB) eq b0) && { txn.set(handleB, b1) ; true }
    }
  }

  @throws(classOf[InterruptedException])
  def cci[A <: AnyRef, B <: AnyRef](handleA: Handle[A], a0: A, handleB: Handle[B], b0: B): Boolean = {
    var tries = 0
    while (tries < 10) {
      val mA0 = handleA.meta
      val mB0 = handleB.meta
      if (!changing(mA0) && !changing(mB0)) {
        val b = handleB.data
        val a = handleA.data
        val mA1 = handleA.meta
        val mB1 = handleB.meta
        if (changingAndVersion(mA0) == changingAndVersion(mA1) && changingAndVersion(mB0) == changingAndVersion(mB1))
          return (a0 eq a) && (b0 eq b)
      }
      if (changing(mA0))
        weakAwaitUnowned(handleA, mA0)
      if (changing(mB0))
        weakAwaitUnowned(handleB, mB0)

      tries += 1
    }

    // fall back on a transaction
    return atomic { t =>
      val txn = t.asInstanceOf[InTxnImpl]
      (txn.get(handleA) eq a0) && (txn.get(handleB) eq b0)
    }
  }

  @throws(classOf[InterruptedException])
  def getAndAdd(handle: Handle[Int], delta: Int): Int = {
    val m0 = acquireLock(handle, true)
    val v0 = handle.data
    commitUpdate(handle, m0, v0 + delta)
    v0
  }
}
