/* scala-stm - (c) 2009-2012, Stanford University, PPL */

package scala.concurrent.stm
package ccstm

import skel._


private[ccstm] abstract class InTxnRefOps extends AccessHistory with AbstractInTxn {
  import CCSTM._
  import Txn._

  //////// abstract txn state

  protected def _barging: Boolean
  protected def _bargeVersion: Version
  protected def _slot: Slot

  //////// abstract methods

  protected def isNewerThanReadVersion(version: Version): Boolean

  protected def revalidate(minNewReadVersion: Version)

  protected def forceRollback(cause: RollbackCause)

  protected def weakAwaitUnowned(handle: Handle[_], m0: Meta)

  //////// lock management - similar to NonTxn but we also check for remote rollback

  /** Calls revalidate(version) if version > _readVersion. */
  private def revalidateIfRequired(version: Version) {
    if (isNewerThanReadVersion(version))
      revalidate(version)
  }

  /** Returns the pre-acquisition metadata. */
  @throws(classOf[InterruptedException])
  private def acquireOwnership(handle: Handle[_]): Meta = {
    var m = handle.meta
    if (owner(m) == _slot)
      return m
    (while (true) {
      if (owner(m) != unownedSlot)
        weakAwaitUnowned(handle, m)
      else if (handle.metaCAS(m, withOwner(m, _slot)))
        return m
      m = handle.meta
    }).asInstanceOf[Nothing]
  }

  private def tryAcquireOwnership(handle: Handle[_], m0: Meta): Boolean = {
    owner(m0) == unownedSlot && handle.metaCAS(m0, withOwner(m0, _slot))
  }

  //////// barrier implementations
  
  @throws(classOf[InterruptedException])
  def get[T](handle: Handle[T]): T = {
    requireActive()

    var m1 = handle.meta
    if (owner(m1) == _slot) {
      // Self-owned.  This particular base+offset might not be in the write
      // buffer, but it's definitely not in anybody else's.
      return stableGet(handle)
    }

    if (readShouldBarge(m1))
      return bargingRead(handle)

    var m0 = 0L
    var value: T = null.asInstanceOf[T]
    do {
      m0 = m1
      while (changing(m0)) {
        weakAwaitUnowned(handle, m0)
        m0 = handle.meta
      }
      revalidateIfRequired(version(m0))
      value = handle.data
      m1 = handle.meta
    } while (changingAndVersion(m0) != changingAndVersion(m1))

    // Stable read.  The second read of handle.meta is required for
    // opacity, and it also enables the read-only commit optimization.
    recordRead(handle, version(m1))
    return value
  }

  private def readShouldBarge(meta: Meta): Boolean = {
    _barging && version(meta) >= _bargeVersion
  }

  @throws(classOf[InterruptedException])
  private def bargingRead[T](handle: Handle[T]): T = {
    val mPrev = acquireOwnership(handle)
    recordBarge(handle)
    revalidateIfRequired(version(mPrev))
    return handle.data
  }

  @throws(classOf[InterruptedException])
  def getWith[T,Z](handle: Handle[T], f: T => Z): Z = {
    if (_barging && version(handle.meta) >= _bargeVersion)
      return f(get(handle))

    requireActive()
    val u = unrecordedRead(handle)
    val result = f(u.value)
    if (!u.recorded) {
      val callback = new Function[NestingLevel, Unit] {
        var _latestRead = u

        def apply(level: NestingLevel) {
          if (!isValid)
            level.requestRollback(OptimisticFailureCause('invalid_getWith, Some(handle)))
        }

        private def isValid: Boolean = {
          if (_latestRead == null || _latestRead.stillValid)
            return true

          val m1 = handle.meta
          if (owner(m1) == _slot) {
            // We know that our original read did not come from the write
            // buffer, because !u.recorded.  That means that to redo this
            // read we should go to handle.data, which has the most recent
            // value from which we should read.
            _latestRead = null
            return (result == f(handle.data))
          }

          // reread, and see if that changes the result
          _latestRead = unrecordedRead(handle)

          return (result == f(_latestRead.value))
        }
      }

      // It is safe to skip calling callback.valid() here, because we
      // have made no calls into the txn that might have resulted in it
      // moving its virtual snapshot forward.  This means that the
      // unrecorded read that initialized u is consistent with all of the
      // reads performed so far.
      whileValidating(callback)
    }

    return result
  }

  @throws(classOf[InterruptedException])
  def relaxedGet[T](handle: Handle[T], equiv: (T, T) => Boolean): T = {
    if (_barging && version(handle.meta) >= _bargeVersion)
      return get(handle)

    requireActive()
    val u = unrecordedRead(handle)
    val snapshot = u.value
    if (!u.recorded) {
      val callback = new Function[NestingLevel, Unit] {
        var _latestRead = u

        def apply(level: NestingLevel) {
          if (!isValid)
            level.requestRollback(OptimisticFailureCause('invalid_relaxed_get, Some(handle)))
        }

        private def isValid: Boolean = {
          if (_latestRead == null || _latestRead.stillValid)
            return true

          val m1 = handle.meta
          if (owner(m1) == _slot) {
            // We know that our original read did not come from the write
            // buffer, because !u.recorded.  That means that to redo this
            // read we should go to handle.data, which has the most recent
            // value from which we should read.
            _latestRead = null
            return equiv(snapshot, handle.data)
          }

          // reread, and see if that changes the result
          _latestRead = unrecordedRead(handle)

          return equiv(snapshot, _latestRead.value)
        }
      }

      // It is safe to skip calling callback.valid() here, because we
      // have made no calls into the txn that might have resulted in it
      // moving its virtual snapshot forward.  This means that the
      // unrecorded read that initialized u is consistent with all of the
      // reads performed so far.
      whileValidating(callback)
    }

    return snapshot
  }

  @throws(classOf[InterruptedException])
  def unrecordedRead[T](handle: Handle[T]): UnrecordedRead[T] = {
    // unrecorded read might be needed to update validation state of getWith or
    // relaxedGet during the Preparing stage
    requireNotDecided()

    var m1 = handle.meta
    var v: T = null.asInstanceOf[T]
    val rec = (if (owner(m1) == _slot) {
      v = stableGet(handle)
      true
    } else {
      var m0 = 0L
      do {
        m0 = m1
        while (changing(m0)) {
          if (status != Active) {
            // can't wait
            forceRollback(OptimisticFailureCause('late_invalid_unrecordedRead, Some(handle)))
            throw RollbackError
          }
          weakAwaitUnowned(handle, m0)
          m0 = handle.meta
        }
        if (isNewerThanReadVersion(version(m0))) {
          if (status != Active) {
            // can't wait
            forceRollback(OptimisticFailureCause('late_invalid_unrecordedRead, Some(handle)))
            throw RollbackError
          }
          revalidate(version(m0))
        }
        v = handle.data
        m1 = handle.meta
      } while (changingAndVersion(m0) != changingAndVersion(m1))
      false
    })

    new UnrecordedRead[T] {
      def value: T = v
      def stillValid = {
        val m = handle.meta
        version(m) == version(m1) && (!changing(m) || owner(m) == _slot)
      }
      def recorded = rec
    }
  }

  private def freshOwner(mPrev: Meta) = owner(mPrev) == unownedSlot

  @throws(classOf[InterruptedException])
  def set[T](handle: Handle[T], v: T) {
    requireActive()
    val mPrev = acquireOwnership(handle)
    val f = freshOwner(mPrev)
    put(handle, f, v)

    // This might not be a blind write, because meta might be shared with other
    // values that are subsequently read by the transaction.  We don't need to
    // record a read set entry, however, because nobody can modify it after we
    // grab ownership.  This means it suffices to check against _readVersion.
    // We must put something in the buffer before calling revalidate in case we
    // roll back, so that the ownership gets released.
    //
    // If not f, then this was already self-owned.  This particular base+offset
    // might not be in the write buffer, but it's definitely not in anybody
    // else's.
    if (f)
      revalidateIfRequired(version(mPrev))
  }
  
  @throws(classOf[InterruptedException])
  def swap[T](handle: Handle[T], v: T): T = {
    requireActive()
    val mPrev = acquireOwnership(handle)
    val f = freshOwner(mPrev)
    val v0 = swap(handle, f, v)
    if (f)
      revalidateIfRequired(version(mPrev))
    v0
  }

  def trySet[T](handle: Handle[T], v: T): Boolean = {
    requireActive()

    val m0 = handle.meta
    if (owner(m0) == _slot) {
      put(handle, false, v)
      return true
    }

    if (!tryAcquireOwnership(handle, m0))
      return false
    put(handle, true, v)
    revalidateIfRequired(version(m0))
    return true
  }

  @throws(classOf[InterruptedException])
  def compareAndSet[T](handle: Handle[T], before: T, after: T): Boolean = {
    transformIfDefined(handle, new PartialFunction[T,T] {
      def isDefinedAt(v: T): Boolean = before == v
      def apply(v: T): T = after
    })
  }

  @throws(classOf[InterruptedException])
  def compareAndSetIdentity[T, R <: T with AnyRef](handle: Handle[T], before: R, after: T): Boolean = {
    // make a heuristic guess based on a racy read of the value
    if (before eq handle.data.asInstanceOf[AnyRef])
      acquiringCASI(handle, before, after)
    else
      unrecordedCASI(handle, before, after)
  }

  @throws(classOf[InterruptedException])
  private def acquiringCASI[T, R <: T with AnyRef](handle: Handle[T], before: R, after: T): Boolean = {
    requireActive()
    val mPrev = acquireOwnership(handle)
    val f = freshOwner(mPrev)
    val z = compareAndSetIdentity(handle, f, before, after)
    if (f)
      revalidateIfRequired(version(mPrev))
    z
  }

  @throws(classOf[InterruptedException])
  private def unrecordedCASI[T, R <: T with AnyRef](handle: Handle[T], before: R, after: T): Boolean = {
    transformIfDefined(handle, new PartialFunction[T,T] {
      def isDefinedAt(v: T): Boolean = (before eq v.asInstanceOf[AnyRef])
      def apply(v: T): T = after
    })
  }

  @throws(classOf[InterruptedException])
  def getAndTransform[T](handle: Handle[T], func: T => T): T = {
    requireActive()
    val mPrev = acquireOwnership(handle)
    val f = freshOwner(mPrev)
    val v0 = getAndTransform(handle, f, func)
    if (f)
      revalidateIfRequired(version(mPrev))
    v0
  }

  @throws(classOf[InterruptedException])
  def transformAndGet[T](handle: Handle[T], func: T => T): T = {
    requireActive()
    val mPrev = acquireOwnership(handle)
    val f = freshOwner(mPrev)
    val v1 = transformAndGet(handle, f, func)
    if (f)
      revalidateIfRequired(version(mPrev))
    v1
  }

  @throws(classOf[InterruptedException])
  def transformAndExtract[T,V](handle: Handle[T], func: T => (T,V)): V = {
    requireActive()
    val mPrev = acquireOwnership(handle)
    val f = freshOwner(mPrev)
    val v1 = transformAndExtract(handle, f, func)
    if (f)
      revalidateIfRequired(version(mPrev))
    v1
  }

  @throws(classOf[InterruptedException])
  def transformIfDefined[T](handle: Handle[T], pf: PartialFunction[T,T]): Boolean = {
    requireActive()
    val u = unrecordedRead(handle)
    if (!pf.isDefinedAt(u.value)) {
      // make sure it stays undefined
      if (!u.recorded) {        
        val callback = new Function[NestingLevel, Unit] {
          var _latestRead = u

          def apply(level: NestingLevel) {
            if (!isValid)
              level.requestRollback(OptimisticFailureCause('invalid_getWith, Some(handle)))
          }

          private def isValid: Boolean = {
            if (!_latestRead.stillValid) {
              // if defined after reread then return false==invalid
              _latestRead = unrecordedRead(handle)
              !pf.isDefinedAt(_latestRead.value)
            } else {
              true
            }
          }
        }
        whileValidating(callback)
      }
      false
    } else {
      val v = get(handle)
      if (!u.stillValid && !pf.isDefinedAt(v)) {
        // value changed after unrecordedRead
        false
      } else {
        // still defined, do the actual getAndTransform
        set(handle, pf(v))
        true
      }
    }
  }

  @throws(classOf[InterruptedException])
  def getAndAdd(handle: Handle[Int], delta: Int): Int = {
    requireActive()
    val mPrev = acquireOwnership(handle)
    val f = freshOwner(mPrev)
    val v0 = getAndAdd(handle, f, delta)
    if (f)
      revalidateIfRequired(version(mPrev))
    v0
  }

  //////////// TxnLocal stuff

  // We store transactional local values in the write buffer by pretending
  // that they are proper handles, but their data and metadata aren't actually
  // backed by anything.

  def txnLocalFind(local: TxnLocalImpl[_]): Int = findWrite(local)
  def txnLocalGet[T](index: Int): T = getWriteSpecValue[T](index)
  def txnLocalInsert[T](local: TxnLocalImpl[T], v: T) { writeAppend(local, false, v) }
  def txnLocalUpdate[T](index: Int, v: T) { writeUpdate(index, v) }
}
