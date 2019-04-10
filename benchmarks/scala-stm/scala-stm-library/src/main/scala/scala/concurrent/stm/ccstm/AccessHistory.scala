/* scala-stm - (c) 2009-2012, Stanford University, PPL */

package scala.concurrent.stm
package ccstm

import annotation.tailrec

private[ccstm] object AccessHistory {

  /** The operations provided by the read set functionality of an
   *  `AccessHistory`.
   */
  trait ReadSet {
    protected def readCount: Int
    protected def readHandle(i: Int): Handle[_]
    protected def readVersion(i: Int): CCSTM.Version
    protected def recordRead(handle: Handle[_], version: CCSTM.Version)
    protected def readLocate(index: Int): AccessHistory.UndoLog
  }

  /** The operations provided by the pessimistic read set functionality of an
   *  `AccessHistory`.
   */
  trait BargeSet {
    protected def bargeCount: Int
    protected def bargeHandle(i: Int): Handle[_]
    protected def recordBarge(handle: Handle[_])
  }

  /** The operations provided by the write buffer functionality of an
   *  `AccessHistory`.
   */
  trait WriteBuffer {
    protected def writeCount: Int
    protected def getWriteHandle(i: Int): Handle[_]
    protected def getWriteSpecValue[T](i: Int): T
    protected def wasWriteFreshOwner(i: Int): Boolean
    protected def findWrite(handle: Handle[_]): Int
    protected def stableGet[T](handle: Handle[T]): T
    protected def put[T](handle: Handle[T], freshOwner: Boolean, value: T)
    protected def writeAppend[T](handle: Handle[T], freshOwner: Boolean, v: T)
    protected def writeUpdate[T](i: Int, v: T)
    protected def swap[T](handle: Handle[T], freshOwner: Boolean, value: T): T
    protected def compareAndSetIdentity[T, R <: T with AnyRef](
        handle: Handle[T], freshOwner: Boolean, before: R, after: T): Boolean
    protected def getAndTransform[T](handle: Handle[T], freshOwner: Boolean, func: T => T): T
    protected def transformAndGet[T](handle: Handle[T], freshOwner: Boolean, func: T => T): T
    protected def transformAndExtract[T,V](handle: Handle[T], freshOwner: Boolean, func: T => (T,V)): V
    protected def getAndAdd(handle: Handle[Int], freshOwner: Boolean, delta: Int): Int
  }

  /** Holds the write buffer undo log for a particular nesting level.  This is
   *  exposed as an abstract class so that the different parts of the STM that
   *  have per-nesting level objects can share a single instance.
   */
  abstract class UndoLog {
    def parUndo: UndoLog

    var minRetryTimeoutNanos = Long.MaxValue
    var consumedRetryDelta = 0L
    var prevReadCount = 0
    var prevBargeCount = 0
    var prevWriteThreshold = 0

    def addRetryTimeoutNanos(timeoutNanos: Long) {
      minRetryTimeoutNanos = math.min(minRetryTimeoutNanos, timeoutNanos)
    }

    /** Returns the sum of the timeouts of the retries that have timed out.
     *  Included levels are this one, parents of this one, levels that have
     *  been merged into an included level, and levels that were ended with a
     *  permanent rollback and whose parent was included.
     */
    @tailrec final def consumedRetryTotal(accum: Long = 0L): Long = {
      val z = accum + consumedRetryDelta
      if (parUndo == null) z else parUndo.consumedRetryTotal(z)
    }

    @tailrec final def readLocate(index: Int): UndoLog = {
      if (index >= prevReadCount) this else parUndo.readLocate(index)
    }

    private var _logSize = 0
    private var _indices: Array[Int] = null
    private var _prevValues: Array[AnyRef] = null

    def logWrite(i: Int, v: AnyRef) {
      if (_indices == null || _logSize == _indices.length)
        grow()
      _indices(_logSize) = i
      _prevValues(_logSize) = v
      _logSize += 1
    }

    private def grow() {
      if (_logSize == 0) {
        _indices = new Array[Int](16)
        _prevValues = new Array[AnyRef](16)
      } else {
        _indices = copyTo(_indices, new Array[Int](_indices.length * 2))
        _prevValues = copyTo(_prevValues, new Array[AnyRef](_prevValues.length * 2))
      }
    }

    private def copyTo[A](src: Array[A], dst: Array[A]): Array[A] = {
      System.arraycopy(src, 0, dst, 0, src.length)
      dst
    }

    def undoWrites(hist: AccessHistory) {
      // it is important to apply in reverse order
      var i = _logSize - 1
      while (i >= 0) {
        hist.setSpecValue(_indices(i), _prevValues(i))
        i -= 1
      }
    }
  }
}

/** `AccessHistory` includes the read set and the write buffer for all
 *  transaction levels that have not been rolled back.  The read set is a
 *  linear log that contains duplicates, rollback consists of truncating the
 *  read log.  The write buffer is a hash table in which the entries are
 *  addressed by index, rather than by Java reference.  Indices are allocated
 *  sequentially, so a high-water mark (_wUndoThreshold) can differentiate
 *  between entries that can be discarded on a partial rollback and those that
 *  need to be reverted to a previous value.  An undo log is maintained for
 *  writes to entries from enclosing nesting levels, but it is expected that
 *  common usage will be handled mostly using the high-water mark.
 *
 *  It is intended that this class can be extended by the actual `InTxn`
 *  implementation to reduce levels of indirection during barriers.  This is a
 *  bit clumsy, and results in verbose method names to differentiate between
 *  overlapping operations.  Please look away as the sausage is made.  To help
 *  tame the mess the read set and write buffer interfaces are separated into
 *  traits housed in the companion object.  This doesn't actually increase
 *  modularity, but serves as compile-time-checked documentation.
 *
 *  @author Nathan Bronson
 */
private[ccstm] abstract class AccessHistory extends AccessHistory.ReadSet with AccessHistory.BargeSet with AccessHistory.WriteBuffer {

  protected def undoLog: AccessHistory.UndoLog

  protected def checkpointAccessHistory(reusedReadThreshold: Int) {
    checkpointReadSet(reusedReadThreshold)
    checkpointBargeSet()
    checkpointWriteBuffer()
  }

  protected def mergeAccessHistory() {
    // nested commit
    if (Stats.nested != null)
      recordMerge()

    mergeRetryTimeout()
    mergeWriteBuffer()
  }

  private def recordMerge() {
    Stats.nested.commits += 1
  }

  /** Releases locks for discarded handles */
  protected def rollbackAccessHistory(slot: CCSTM.Slot, cause: Txn.RollbackCause) {
    // nested or top-level rollback
    if (Stats.top != null)
      recordRollback(cause)

    if (!cause.isInstanceOf[Txn.ExplicitRetryCause]) {
      rollbackReadSet()
      rollbackBargeSet(slot)
    }
    rollbackRetryTimeout(cause)
    rollbackWriteBuffer(slot)
  }

  private def recordRollback(cause: Txn.RollbackCause) {
    val stat = if (undoLog.parUndo == null) Stats.top else Stats.nested
    stat.rollbackReadSet += (readCount - undoLog.prevReadCount)
    stat.rollbackBargeSet += (bargeCount - undoLog.prevBargeCount)
    stat.rollbackWriteSet += (writeCount - undoLog.prevWriteThreshold)
    cause match {
      case Txn.ExplicitRetryCause(_) => stat.explicitRetries += 1
      case Txn.OptimisticFailureCause(tag, _) => stat.optimisticRetries += tag
      case Txn.UncaughtExceptionCause(x) => stat.failures += x.getClass
      case Txn.UnrecordedTxnCause(_) => stat.unrecordedTxns += 1
    }
  }

  /** Does not release locks */
  protected def resetAccessHistory() {
    if (Stats.top != null)
      recordTopLevelCommit()

    resetReadSet()
    resetBargeSet()
    resetWriteBuffer()
  }

  private def recordTopLevelCommit() {
    // top-level commit
    val top = Stats.top
    top.commitReadSet += readCount
    top.commitBargeSet += bargeCount
    top.commitWriteSet += writeCount
    top.commits += 1
  }

  /** Clears the read set and barge set, returning a `RetrySet` that holds the
   *  values that were removed.  Releases any ownership held by the barge set.
   */
  protected def takeRetrySet(slot: CCSTM.Slot): RetrySet = {
    // barge entries were copied to the read set by addLatestWritesAsReads
    var i = 0
    while (i < _bCount) {
      rollbackHandle(_bHandles(i), slot)
      i += 1
    }
    resetBargeSet()

    val accum = new RetrySetBuilder
    i = 0
    while (i < _rCount) {
      accum += (_rHandles(i), _rVersions(i))
      i += 1
    }
    resetReadSet()
    accum.result()
  }


  //////////// retry timeout

  private def mergeRetryTimeout() {
    // nested commit
    val u = undoLog
    val p = u.parUndo
    p.addRetryTimeoutNanos(u.minRetryTimeoutNanos)
    p.consumedRetryDelta += u.consumedRetryDelta
  }

  private def rollbackRetryTimeout(cause: Txn.RollbackCause) {
    cause match {
      case Txn.ExplicitRetryCause(timeoutNanos) => {
        if (!timeoutNanos.isEmpty)
          undoLog.addRetryTimeoutNanos(timeoutNanos.get)
        if (undoLog.parUndo != null)
          undoLog.parUndo.addRetryTimeoutNanos(undoLog.minRetryTimeoutNanos)
      }
      case _: Txn.PermanentRollbackCause => {
        if (undoLog.parUndo != null)
          undoLog.parUndo.consumedRetryDelta += undoLog.consumedRetryDelta
      }
      case _ =>
    }
  }

  //////////// read set

  private final val InitialReadCapacity = 1024
  private final val MaxRetainedReadCapacity = 8 * InitialReadCapacity

  private var _rCount = 0
  private var _rHandles: Array[Handle[_]] = null
  private var _rVersions: Array[CCSTM.Version] = null
  allocateReadSet()

  protected def readCount = _rCount
  protected def readHandle(i: Int): Handle[_] = _rHandles(i)
  protected def readVersion(i: Int): CCSTM.Version = _rVersions(i)

  protected def recordRead(handle: Handle[_], version: CCSTM.Version) {
    val i = _rCount
    if (i == _rHandles.length)
      growReadSet()
    _rHandles(i) = handle
    _rVersions(i) = version
    _rCount = i + 1
  }

  private def growReadSet() {
    _rHandles = copyTo(_rHandles, new Array[Handle[_]](_rHandles.length * 2))
    _rVersions = copyTo(_rVersions, new Array[CCSTM.Version](_rVersions.length * 2))
  }

  private def copyTo[A](src: Array[A], dst: Array[A]): Array[A] = {
    System.arraycopy(src, 0, dst, 0, src.length)
    dst
  }

  private def checkpointReadSet(reusedReadThreshold: Int) {
    undoLog.prevReadCount = if (reusedReadThreshold >= 0) reusedReadThreshold else _rCount
  }

  private def rollbackReadSet() {
    val n = undoLog.prevReadCount
    var i = n
    while (i < _rCount) {
      _rHandles(i) = null
      i += 1
    }
    _rCount = n
  }

  private def resetReadSet() {
    if (_rHandles.length > MaxRetainedReadCapacity) {
      // avoid staying very large
      allocateReadSet()
    } else {
      // allow GC of old handles
      var i = 0
      while (i < _rCount) {
        _rHandles(i) = null
        i += 1
      }
    }
    _rCount = 0
  }

  private def allocateReadSet() {
    _rHandles = new Array[Handle[_]](InitialReadCapacity)
    _rVersions = new Array[CCSTM.Version](InitialReadCapacity)
  }

  protected def readLocate(index: Int): AccessHistory.UndoLog = undoLog.readLocate(index)


  //////////// pessimistic read buffer

  private final val InitialBargeCapacity = 1024
  private final val MaxRetainedBargeCapacity = 8 * InitialBargeCapacity

  private var _bCount = 0
  private var _bHandles: Array[Handle[_]] = null
  allocateBargeSet()

  protected def bargeCount = _bCount
  protected def bargeHandle(i: Int): Handle[_] = _bHandles(i)

  protected def recordBarge(handle: Handle[_]) {
    val i = _bCount
    if (i == _bHandles.length)
      growBargeSet()
    _bHandles(i) = handle
    _bCount = i + 1
  }

  private def growBargeSet() {
    _bHandles = copyTo(_bHandles, new Array[Handle[_]](_bHandles.length * 2))
  }

  private def checkpointBargeSet() {
    undoLog.prevBargeCount = _bCount
  }

  private def rollbackBargeSet(slot: CCSTM.Slot) {
    val n = undoLog.prevBargeCount
    var i = n
    while (i < _bCount) {
      rollbackHandle(_bHandles(i), slot)
      _bHandles(i) = null
      i += 1
    }
    _bCount = n
  }

  private def resetBargeSet() {
    if (_bCount > 0)
      resetBargeSetNonEmpty()
  }

  private def resetBargeSetNonEmpty() {
    if (_bHandles.length > MaxRetainedBargeCapacity) {
      // avoid staying very large
      allocateBargeSet()
    } else {
      // allow GC of old handles
      var i = 0
      while (i < _bCount) {
        _bHandles(i) = null
        i += 1
      }
    }
    _bCount = 0
  }

  private def allocateBargeSet() {
    _bHandles = new Array[Handle[_]](InitialBargeCapacity)
  }


  //////////// write buffer

  private final val InitialWriteCapacity = 8
  private final val MinAllocatedWriteCapacity = 512
  private final val MaxRetainedWriteCapacity = 8 * MinAllocatedWriteCapacity

  // This write buffer implementation uses chaining, but instead of storing the
  // buckets in objects, they are packed into the arrays bucketAnys and
  // bucketInts.  Pointers to a bucket are represented as a 0-based int, with
  // -1 representing nil.  The dispatch array holds the entry index for the
  // beginning of a bucket chain.
  //
  // When a nested context is created with push(), the current number of
  // allocated buckets is recorded in undoThreshold.  Any changes to the
  // speculative value for a bucket with an index less than this threshold are
  // logged to allow partial rollback.  Buckets with an index greater than the
  // undoThreshold can be discarded during rollback.  This means that despite
  // nesting, each <base,offset> key is stored at most once in the write buffer.

  /** The maximum index for which undo entries are required. */
  private var _wUndoThreshold = 0

  private var _wCount = 0
  private var _wCapacity = InitialWriteCapacity
  private var _wAnys: Array[AnyRef] = null
  private var _wInts: Array[Int] = null
  private var _wDispatch: Array[Int] = null
  allocateWriteBuffer()

  private def allocateWriteBuffer() {
    _wAnys = new Array[AnyRef](bucketAnysLen(MinAllocatedWriteCapacity))
    _wInts = new Array[Int](bucketIntsLen(MinAllocatedWriteCapacity))
    _wDispatch = new Array[Int](MinAllocatedWriteCapacity)
    java.util.Arrays.fill(_wDispatch, 0, InitialWriteCapacity, -1)
  }

  private def refI(i: Int) = 3 * i
  private def specValueI(i: Int) = 3 * i + 1
  private def handleI(i: Int) = 3 * i + 2
  private def offsetI(i: Int) = 2 * i
  private def nextI(i: Int) = 2 * i + 1 // bits 31..1 are the next, bit 0 is set iff freshOwner

  private def bucketAnysLen(c: Int) = 3 * (maxSizeForCap(c) + 1)
  private def bucketIntsLen(c: Int) = 2 * (maxSizeForCap(c) + 1)

  private def maxSizeForCap(c: Int) = c - c / 4
  private def shouldGrow(s: Int, c: Int): Boolean = s > maxSizeForCap(c)
  private def shouldGrow: Boolean = shouldGrow(_wCount, _wCapacity)
  private def shouldShrink(s: Int, c: Int): Boolean = c > InitialWriteCapacity && !shouldGrow(s, c / 4)
  private def shouldShrink: Boolean = shouldShrink(_wCount, _wCapacity)

  //////// accessors

  private def getRef(i: Int) = _wAnys(refI(i))
  final protected def getWriteHandle(i: Int) = _wAnys(handleI(i)).asInstanceOf[Handle[_]]
  final protected def getWriteSpecValue[T](i: Int) = _wAnys(specValueI(i)).asInstanceOf[T]
  private def getOffset(i: Int) = _wInts(offsetI(i))
  private def getNext(i: Int): Int = _wInts(nextI(i)) >> 1
  final protected def wasWriteFreshOwner(i: Int): Boolean = (_wInts(nextI(i)) & 1) != 0

  private def setRef(i: Int, r: AnyRef) { _wAnys(refI(i)) = r }
  private def setHandle(i: Int, h: Handle[_]) { _wAnys(handleI(i)) = h }
  final private[AccessHistory] def setSpecValue[T](i: Int, v: T) { _wAnys(specValueI(i)) = v.asInstanceOf[AnyRef] }
  private def setOffset(i: Int, o: Int) { _wInts(offsetI(i)) = o }
  private def setNextAndFreshOwner(i: Int, n: Int, freshOwner: Boolean) { _wInts(nextI(i)) = (n << 1) | (if (freshOwner) 1 else 0) }
  private def setNext(i: Int, n: Int) { _wInts(nextI(i)) = (n << 1) | (_wInts(nextI(i)) & 1) }
  private def setFreshOwner(i: Int, freshOwner: Boolean) { setNextAndFreshOwner(i, getNext(i), freshOwner) }

  //////// bulk access

  protected def writeCount = _wCount

  //////// reads

  /** Reads a handle that is owned by this InTxnImpl family. */
  protected def stableGet[T](handle: Handle[T]): T = {
    val i = findWrite(handle)
    if (i >= 0) {
      // hit
      getWriteSpecValue[T](i)
    } else {
      // miss (due to shared metadata)
      handle.data
    }
  }

  protected def findWrite(handle: Handle[_]): Int = {
    val base = handle.base
    val offset = handle.offset
    find(base, offset, computeSlot(base, offset))
  }

  private def computeSlot(base: AnyRef, offset: Int): Int = {
    if (_wCapacity == InitialWriteCapacity) 0 else CCSTM.hash(base, offset) & (_wCapacity - 1)
  }

  private def find(base: AnyRef, offset: Int, slot: Int): Int = {
    var i = _wDispatch(slot)
    while (i >= 0 && ((base ne getRef(i)) || offset != getOffset(i)))
      i = getNext(i)
    i
  }

  //////// writes

  protected def put[T](handle: Handle[T], freshOwner: Boolean, value: T) {
    val base = handle.base
    val offset = handle.offset
    val slot = computeSlot(base, offset)
    val i = find(base, offset, slot)
    if (i >= 0) {
      //assert(!freshOwner)
      // hit, update an existing entry, optionally with undo
      if (i < _wUndoThreshold)
        undoLog.logWrite(i, getWriteSpecValue(i))
      setSpecValue(i, value)
    } else {
      // miss, create a new entry
      append(base, offset, handle, freshOwner, value, slot)
    }
  }

  protected def swap[T](handle: Handle[T], freshOwner: Boolean, value: T): T = {
    val i = findOrAllocate(handle, freshOwner)
    val before = getWriteSpecValue[T](i)
    setSpecValue(i, value)
    return before
  }

  protected def compareAndSetIdentity[T, R <: T with AnyRef](
      handle: Handle[T], freshOwner: Boolean, before: R, after: T): Boolean = {
    val i = findOrAllocate(handle, freshOwner)
    val v0 = getWriteSpecValue[T](i)
    if (before eq v0.asInstanceOf[AnyRef]) {
      setSpecValue(i, after)
      return true
    } else {
      return false
    }
  }

  protected def getAndTransform[T](handle: Handle[T], freshOwner: Boolean, func: T => T): T = {
    val i = findOrAllocate(handle, freshOwner)
    val before = getWriteSpecValue[T](i)
    setSpecValue(i, func(before))
    return before
  }

  protected def transformAndGet[T](handle: Handle[T], freshOwner: Boolean, func: T => T): T = {
    val i = findOrAllocate(handle, freshOwner)
    val after = func(getWriteSpecValue[T](i))
    setSpecValue(i, after)
    return after
  }

  protected def transformAndExtract[T,V](handle: Handle[T], freshOwner: Boolean, func: T => (T,V)): V = {
    val i = findOrAllocate(handle, freshOwner)
    val pair = func(getWriteSpecValue[T](i))
    setSpecValue(i, pair._1)
    return pair._2
  }

  protected def getAndAdd(handle: Handle[Int], freshOwner: Boolean, delta: Int): Int = {
    val i = findOrAllocate(handle, freshOwner)
    val before = getWriteSpecValue[Int](i)
    setSpecValue(i, before + delta)
    return before
  }

  protected def writeAppend[T](handle: Handle[T], freshOwner: Boolean, value: T) {
    val base = handle.base
    val offset = handle.offset
    val slot = computeSlot(base, offset)
    append(base, offset, handle, freshOwner, value, slot)
  }

  protected def writeUpdate[T](i: Int, value: T) {
    if (i < _wUndoThreshold)
      undoLog.logWrite(i, getWriteSpecValue(i))
    setSpecValue(i, value)
  }

  private def findOrAllocate(handle: Handle[_], freshOwner: Boolean): Int = {
    val base = handle.base
    val offset = handle.offset
    val slot = computeSlot(base, offset)
    if (!freshOwner) {
      val i = find(base, offset, slot)
      if (i >= 0) {
        // hit, undo log entry is required to capture the potential reads that
        // won't be recorded in this nested txn's read set
        if (i < _wUndoThreshold)
          undoLog.logWrite(i, getWriteSpecValue(i))
        return i
      }
    }

    // miss, create a new entry using the existing data value
    return append(base, offset, handle, freshOwner, handle.data, slot)
  }

  private def append(base: AnyRef, offset: Int, handle: Handle[_], freshOwner: Boolean, value: Any, slot: Int): Int = {
    val i = _wCount
    setRef(i, base)
    setSpecValue(i, value)
    setHandle(i, handle)
    setOffset(i, offset)
    setNextAndFreshOwner(i, _wDispatch(slot), freshOwner)
    _wDispatch(slot) = i
    _wCount = i + 1

    if (shouldGrow)
      grow()

    // grow() relinks the buckets but doesn't move them, so i is still valid
    return i
  }

  private def grow() {
    // adjust capacity
    _wCapacity *= 2
    if (_wCapacity > _wDispatch.length) {
      // we actually need to reallocate
      _wAnys = copyTo(_wAnys, new Array[AnyRef](bucketAnysLen(_wCapacity)))
      _wInts = copyTo(_wInts, new Array[Int](bucketIntsLen(_wCapacity)))
      _wDispatch = new Array[Int](_wCapacity)
    }
    rebuildDispatch()
  }

  private def rebuildDispatch() {
    java.util.Arrays.fill(_wDispatch, 0, _wCapacity, -1)

    var i = 0
    while (i < _wCount) {
      val slot = computeSlot(getRef(i), getOffset(i))
      setNext(i, _wDispatch(slot))
      _wDispatch(slot) = i
      i += 1
    }
  }

  //////// nesting management and visitation

  private def checkpointWriteBuffer() {
    undoLog.prevWriteThreshold = _wUndoThreshold
    _wUndoThreshold = _wCount
  }

  private def mergeWriteBuffer() {
    _wUndoThreshold = undoLog.prevWriteThreshold
  }

  private def rollbackWriteBuffer(slot: CCSTM.Slot) {
    // restore the specValue-s modified in pre-existing write buffer entries
    undoLog.undoWrites(this)

    var i = _wCount - 1
    val e = _wUndoThreshold
    val completeRelink = i >= 2 * e // faster to reprocess remaining entries?
    while (i >= e) {
      // unlock
      if (wasWriteFreshOwner(i))
        rollbackHandle(getWriteHandle(i), slot)

      // unlink
      if (!completeRelink) {
        _wDispatch(computeSlot(getRef(i), getOffset(i))) = getNext(i)
      }

      // discard references to aid GC
      setRef(i, null)
      setSpecValue(i, null)
      setHandle(i, null)

      i -= 1
    }
    _wCount = e

    if (completeRelink) {
      while (shouldShrink)
        _wCapacity /= 2
      rebuildDispatch()
    }

    // revert to previous context
    _wUndoThreshold = undoLog.prevWriteThreshold
  }

  protected def rollbackHandle(h: Handle[_], slot: CCSTM.Slot) { rollbackHandle(h, slot, h.meta) }

  protected def rollbackHandle(h: Handle[_], slot: CCSTM.Slot, m0: CCSTM.Meta) {
    // we must use CAS because there can be concurrent pendingWaiter adds
    // and concurrent "helpers" that release the lock
    var m = m0
    while (CCSTM.owner(m) == slot && !h.metaCAS(m, CCSTM.withRollback(m)))
      m = h.meta
  }

  private def resetWriteBuffer() {
    if (_wCount > 0)
      resetWriteBufferNonEmpty()
  }

  private def resetWriteBufferNonEmpty() {
    if (_wDispatch.length > MaxRetainedWriteCapacity) {
      allocateWriteBuffer()
    } else {
      val n = bucketAnysLen(_wCount)
      var i = 0
      while (i < n) {
        // discard references to aid GC
        _wAnys(i) = null
        i += 1
      }
      i = 0
      while (i < InitialWriteCapacity) {
        _wDispatch(i) = -1
        i += 1
      }
      //java.util.Arrays.fill(_wAnys, 0, bucketAnysLen(_wCount), null)
      //java.util.Arrays.fill(_wDispatch, 0, InitialWriteCapacity, -1)
    }
    _wCount = 0
    _wCapacity = InitialWriteCapacity
  }

  protected def addLatestWritesAsReads(convertToBarge: Boolean) {
    // we need to capture the version numbers from barges
    var i = undoLog.prevBargeCount
    while (i < _bCount) {
      val h = _bHandles(i)
      recordRead(h, CCSTM.version(h.meta))
      i += 1
    }

    i = _wUndoThreshold
    while (i < _wCount) {
      val h = getWriteHandle(i)
        // we only need one entry in the read set per meta
      if (wasWriteFreshOwner(i)) {
        recordRead(h, CCSTM.version(h.meta))
        if (convertToBarge) {
          setFreshOwner(i, false)
          recordBarge(h)
        }
      }
      i += 1
    }
  }
}

