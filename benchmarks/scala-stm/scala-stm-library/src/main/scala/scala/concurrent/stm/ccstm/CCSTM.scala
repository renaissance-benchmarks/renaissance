/* scala-stm - (c) 2009-2012, Stanford University, PPL */

package scala.concurrent.stm
package ccstm

import java.util.concurrent.TimeUnit

private[ccstm] object CCSTM extends GV6 {

  /** The number of times to spin tightly when waiting for a condition to
   *  become true.
   */
  val SpinCount = System.getProperty("ccstm.spin", "100").toInt

  /** The number of times to spin tightly when waiting for another thread to
   *  perform work that we can also perform.
   */
  val StealSpinCount = System.getProperty("ccstm.steal.spin", "10").toInt

  /** The number of times to spin with intervening calls to
   *  `Thread.yield` when waiting for a condition to become true.
   *  These spins will occur after the `SpinCount` spins.  After
   *  `SpinCount + YieldCount` spins have been performed, the
   *  waiting thread will be blocked on a Java mutex.
   */
  val YieldCount = System.getProperty("ccstm.yield", "2").toInt

  /** The number of optimistic failures to tolerate before switching to
   *  pessimistic reads for recently modified memory locations.  Set to zero to
   *  always use pessimistic reads for memory locations modified since the
   *  beginning of the first transaction attempt.
   */
  val BargeRecentThreshold = System.getProperty("ccstm.barge.recent.threshold", "3").toInt

  /** The number of optimistic failures to tolerate before switching to
   *  pessimistic reads for all reads.  Set to zero to always use pessimistic
   *  reads.
   */
  val BargeAllThreshold = System.getProperty("ccstm.barge.all.threshold", "30").toInt

  /** `slotManager` maps slot number to root `TxnLevelImpl`. */
  val slotManager = new TxnSlotManager[TxnLevelImpl](2048, 2)
  val wakeupManager = new WakeupManager // default size

  /** Hashes `base` with `offset`. */
  def hash(base: AnyRef, offset: Int): Int = hash(base) ^ (0x40108097 * offset)

  /** Hashes `base` using its identity hash code. */
  def hash(base: AnyRef): Int = {
    val h = System.identityHashCode(base)
    // multiplying by -127 is recommended by java.util.IdentityHashMap
    h - (h << 7)
  }

  //////////////// Metadata bit packing

  // metadata bits are:
  //  63 = locked for change
  //  62 = pending wakeups
  //  51..61 = owner slot
  //  0..50 = version
  type Meta = Long
  type Slot = Int
  type Version = Long

  /** The slot number used when a memory location has not been reserved or
   *  locked for writing.
   */
  def unownedSlot: Slot = 0

  /** The slot number used by non-transactional code that reserves or locks
   *  a location for writing.
   */
  def nonTxnSlot: Slot = 1

  def txnLocalMeta: Meta = withChanging(withVersion(0L, (1L << 51) - 2))

  // TODO: clean up the following mess
  
  def owner(m: Meta): Slot = (m >> 51).asInstanceOf[Int] & 2047
  def version(m: Meta): Version = (m & ((1L << 51) - 1))
  def pendingWakeups(m: Meta): Boolean = (m & (1L << 62)) != 0
  def changing(m: Meta): Boolean = m < 0

  // masks off owner and pendingWakeups
  def changingAndVersion(m: Meta) = m & ((1L << 63) | ((1L << 51) - 1))
  def ownerAndVersion(m: Meta) = m & ((2047L << 51) | ((1L << 51) - 1))

  def withOwner(m: Meta, o: Slot): Meta = (m & ~(2047L << 51)) | (o.asInstanceOf[Long] << 51)
  def withUnowned(m: Meta): Meta = withOwner(m, unownedSlot)
  def withVersion(m: Meta, ver: Version) = (m & ~((1L << 51) - 1)) | ver

  /** It is not allowed to set PendingWakeups if Changing. */
  def withPendingWakeups(m: Meta): Meta = m | (1L << 62)
  def withChanging(m: Meta): Meta = m | (1L << 63)
  def withUnchanging(m: Meta): Meta = m & ~(1L << 63)

  /** Clears all of the bits except the version. */
  def withCommit(m: Meta, ver: Version) = ver

  /** Includes withUnowned and withUnchanging. */
  def withRollback(m: Meta) = withUnowned(withUnchanging(m))

//  //////////////// Version continuity between separate Refs
//
//  private def CryptMask = 31
//  private val crypts = Array.tabulate(CryptMask + 1)(_ => new AtomicLong)
//
//  def embalm(identity: Int, handle: Handle[_]) {
//    val crypt = crypts(identity & CryptMask)
//    val v = version(handle.meta)
//    var old = crypt.get
//    while (v > old && !crypt.compareAndSet(old, v))
//      old = crypt.get
//  }
//
//  def resurrect(identity: Int, handle: Handle[_]) {
//    val v0 = crypts(identity & CryptMask).get
//    if (!handle.metaCAS(0L, withVersion(0L, v0))) {
//      throw new IllegalStateException("Refs may only be resurrected into an old identity before use")
//    }
//    handle.meta = withVersion(0L, v0)
//  }

  //////////////// lock release helping

  def stealHandle(handle: Handle[_], m0: Meta, owningRoot: TxnLevelImpl) {

    // We can definitely make forward progress below at the expense of a
    // couple of extra CAS, so it is not useful for us to do a big spin with
    // yields.
    var spins = 0
    do {
      val m = handle.meta
      if (ownerAndVersion(m) != ownerAndVersion(m0))
        return // no steal needed

      spins += 1
    } while (spins < StealSpinCount)

    // If owningRoot has been doomed it might be a while before it releases its
    // lock on the handle.  Slot numbers are reused, however, so we have to
    // manage a reference count on the slot while we steal the handle.  This is
    // expensive, which is why we just spun.

    val owningSlot = owner(m0)
    val o = slotManager.beginLookup(owningSlot)
    try {
      if (o ne owningRoot)
        return // owningRoot unregistered itself, so it has already released all locks

      while (true) {
        val m = handle.meta
        if (ownerAndVersion(m) != ownerAndVersion(m0) || handle.metaCAS(m, withRollback(m)))
          return // no longer locked, or steal succeeded
      }
    } finally {
      slotManager.endLookup(owningSlot, o)
    }
  }

  //////////////// lock waiting

  /** Once `handle.meta` has been unlocked since a time it had
   *  value `m0`, the method will return.  It might return sooner,
   *  but an attempt is made to do the right thing.  If `currentTxn`
   *  is non-null, `currentTxn.requireActive` will be called before
   *  blocking and `currentTxn.resolveWriteWriteConflict` will be
   *  called before waiting for a transaction.
   */
  @throws(classOf[InterruptedException])
  def weakAwaitUnowned(handle: Handle[_], m0: Meta, currentTxn: TxnLevelImpl) {
    if (owner(m0) == nonTxnSlot)
      weakAwaitNonTxnUnowned(handle, m0, currentTxn)
    else
      weakAwaitTxnUnowned(handle, m0, currentTxn)
  }

  @throws(classOf[InterruptedException])
  private def weakAwaitNonTxnUnowned(handle: Handle[_], m0: Meta, currentTxn: TxnLevelImpl) {
    // Non-transaction owners only set the changing bit for a short time (no
    // user code and no loops), so we just wait them out.  Previously we used
    // the wakeup mechanism, but that requires all non-txn lock releases to use
    // CAS.

    var spins = 0
    while (true) {
      spins += 1
      if (spins > SpinCount) {
        if (Thread.interrupted)
          throw new InterruptedException
        Thread.`yield`
      }

      val m = handle.meta
      if (ownerAndVersion(m) != ownerAndVersion(m0)) 
        return

      if (null != currentTxn)
        currentTxn.requireActive()
    }
  }

  @throws(classOf[InterruptedException])
  private def weakAwaitTxnUnowned(handle: Handle[_], m0: Meta, currentTxn: TxnLevelImpl) {
    if (null == currentTxn) {
      // Spin a bit, but only from a non-txn context.  If this is a txn context
      // We need to roll ourself back ASAP if that is the proper resolution.
      var spins = 0
      while (spins < SpinCount + YieldCount) {
        spins += 1
        if (spins > SpinCount)
          Thread.`yield`

        val m = handle.meta
        if (ownerAndVersion(m) != ownerAndVersion(m0))
          return

        if (null != currentTxn)
          currentTxn.requireActive()
      }
    }

    // to wait for a txn owner, we track down the InTxnImpl and wait on it
    val owningSlot = owner(m0)
    val owningRoot = slotManager.beginLookup(owningSlot)
    try {
      if (null != owningRoot && owningSlot == owner(handle.meta)) {
        if (!owningRoot.status.completed) {
          if (null != currentTxn)
            currentTxn.txn.resolveWriteWriteConflict(owningRoot, handle)
//          else if (owningRoot.txn == InTxnImpl.get) {
//            // We are in an escaped context and are waiting for a txn that is
//            // attached to this thread.  Big trouble!
//            assert(false) // CCSTM on top of scala-stm doesn't have escaped contexts, this shouldn't happen
//            owningRoot.requestRollback(
//                Txn.OptimisticFailureCause('conflicting_reentrant_nontxn_write, Some(handle)))
//          }

          owningRoot.awaitCompleted(currentTxn, handle)
          if (currentTxn != null)
            currentTxn.requireActive()
        }

        // we've already got the beginLookup, so no need to do a standalone
        // stealHandle
        var m = 0L
        do {
          m = handle.meta
          assert(ownerAndVersion(m) != ownerAndVersion(m0) || owningRoot.status.isInstanceOf[Txn.RolledBack])
        } while (ownerAndVersion(m) == ownerAndVersion(m0) && !handle.metaCAS(m, withRollback(m)))

        // no longer locked, or steal succeeded
      }
    } finally {
      slotManager.endLookup(owningSlot, owningRoot)
    }
  }
}

/** The reference STM implementation for `scala.concurrent.stm`.  CCSTM is a
 *  library-only STM based on the SwissTM algorithm, extended to reduce the
 *  overhead of non-transactional accesses, allow partial rollback, and include
 *  modular blocking and composition operators `retry` and `orAtomic`.
 *
 *  During construction the system property "ccstm.stats" is checked.  If it is
 *  "true" or "1" (actually if it starts with any of the characters 't', 'T',
 *  'y', 'Y', or '1') then statistics are recorded while the program runs and
 *  printed to `Console` during JVM shutdown.
 *
 *  Statistics are tracked separately for top-level transactions and true
 *  nested transactions.  Many nested atomic blocks can be merged into the
 *  top-level transaction by CCSTM for efficiency; these are not reported as
 *  nested.
 *
 *  Reported statistics are either counts or exponential histograms.  For
 *  histograms `sum` is the sum of the samples, `count` is the number of
 *  transactions for which the statistic was non-zero, `avg` is `sum/count`
 *  and the histogram reports in brackets the number of samples that had a
 *  value of 1, 2..3, 4..7, 8..15, and so on.
 *
 *  Counters:
 *  - `commits` -- committed transactions
 *  - `alternatives` -- alternatives provided to `atomic`, one sample per call
 *    to `atomic`
 *  - `retrySet` -- memory locations watched while performing modular
 *    blocking, one sample per top-level blocking event
 *  - `retryWaitElapsed` -- milliseconds elapsed during modular blocking, one
 *    sample per top-level blocking event
 *  - `explicitRetries` -- explicit retries using `retry`, `retryFor`,
 *    `Ref.View.await` or `Ref.View.tryAwait`
 *  - `unrecordedTxns` -- rollbacks that were to erase a successful use of
 *    `atomic.unrecorded`
 *  - `optimisticRetries` -- rollbacks that were automatically retried, one
 *    line per `OptimisticFailureCause.category`
 *  - `failures` -- rollbacks that were not retried, one line for each type of
 *    exception in `UncaughtExceptionCause`
 *  - `blockingAcquires` -- internal locks that could not be acquired
 *    immediately
 *  - `commitReadSet` -- optimistic `Ref` reads, one sample per committed
 *    top-level transaction
 *  - `commitBargeSet` -- locations read pessimistically, one sample per
 *    committed top-level transaction
 *  - `commitWriteSet` -- locations written, one sample per committed
 *    top-level transaction
 *  - `rollbackReadSet` -- optimistic `Ref` reads, one sample per transaction
 *    that was rolled back
 *  - `rollbackBargeSet` -- locations read pessimistically, one sample per
 *    transaction that was rolled back
 *  - `rollbackWriteSet` -- locations written pessimistically, one sample per
 *    transaction that was rolled back
 *
 *  Read and write set counts for a nested transaction are merged into its
 *  parent if it commits, they are not counted separately during the nested
 *  commit.
 *
 *  @author Nathan Bronson
 */
class CCSTM extends CCSTMExecutor with impl.STMImpl with CCSTMRefs.Factory {
  def findCurrent(implicit mt: MaybeTxn): Option[InTxn] = Option(InTxnImpl.currentOrNull)
  def dynCurrentOrNull: InTxn = InTxnImpl.dynCurrentOrNull

  def newCommitBarrier(timeout: Long, unit: TimeUnit): CommitBarrier =
      new CommitBarrierImpl(unit.toNanos(timeout))
}
