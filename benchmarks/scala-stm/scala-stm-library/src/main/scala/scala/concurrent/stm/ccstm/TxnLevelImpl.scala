/* scala-stm - (c) 2009-2012, Stanford University, PPL */

package scala.concurrent.stm
package ccstm

import scala.annotation.tailrec
import java.util.concurrent.atomic.AtomicReferenceFieldUpdater
import skel.{AbstractNestingLevel, RollbackError}

private[ccstm] object TxnLevelImpl {

  private val stateUpdater = new TxnLevelImpl(null, null, null, false).newStateUpdater

  /** Maps blocked `InTxnImpl` that are members of a commit barrier to the
   *  `TxnLevelImpl` instance on which they are waiting.  All of the values
   *  in this map must be notified when a new link in a (potential) deadlock
   *  chain is formed.
   */
  @volatile private var _blockedBarrierMembers = Map.empty[InTxnImpl, TxnLevelImpl]

  def notifyBlockedBarrierMembers() {
    val m = _blockedBarrierMembers
    if (!m.isEmpty) {
      for (v <- m.values)
        v.synchronized { v.notifyAll() }
    }
  }

  def addBlockedBarrierMember(waiter: InTxnImpl, monitor: TxnLevelImpl) {
    synchronized {
      _blockedBarrierMembers += (waiter -> monitor)
    }
  }

  def removeBlockedBarrierMember(waiter: InTxnImpl) {
    synchronized {
      _blockedBarrierMembers -= waiter
    }
  }
}

/** `TxnLevelImpl` bundles the data and behaviors from `AccessHistory.UndoLog`
 *  and `AbstractNestingLevel`, and adds handling of the nesting level status.
 *
 *  @author Nathan Bronson
 */
private[ccstm] class TxnLevelImpl(val txn: InTxnImpl,
                                  val executor: TxnExecutor,
                                  val parUndo: TxnLevelImpl,
                                  val phantom: Boolean)
        extends AccessHistory.UndoLog with AbstractNestingLevel {
  import TxnLevelImpl._
  import WakeupManager.blocking

  // this is the first non-hidden parent
  val parLevel: AbstractNestingLevel = if (parUndo == null || !parUndo.phantom) parUndo else parUndo.parLevel

  val root: AbstractNestingLevel = if (parLevel == null) this else parLevel.root

  /** The transaction attempt on which this transaction is blocked, if any.
   *  Only set for roots.
   */
  @volatile private var _blockedBy: TxnLevelImpl = null

  /** To make `requireActive` more efficient we store the raw state of
   *  `Txn.Active` as null.  If the raw state is a `TxnLevelImpl`, then that
   *  indicates that this nesting level is an ancestor of `txn.currentLevel`;
   *  this is reported as a status of `Txn.Active`.  The raw state can also be
   *  the interned string value "merged" to indicate that the status is now in
   *  lock-step with the parent.
   */
  @volatile private var _state: AnyRef = null

  private def newStateUpdater: AtomicReferenceFieldUpdater[TxnLevelImpl, AnyRef] = {
    AtomicReferenceFieldUpdater.newUpdater(classOf[TxnLevelImpl], classOf[AnyRef], "_state")
  }

  /** True if anybody is waiting for `status.completed`. */
  @volatile private var _waiters = false

  @tailrec final def minEnclosingRetryTimeout(accum: Long = Long.MaxValue): Long = {
    val z = math.min(accum, executor.retryTimeoutNanos.getOrElse(Long.MaxValue))
    if (parUndo == null) z else parUndo.minEnclosingRetryTimeout(z)
  }

  @tailrec final def status: Txn.Status = {
    val raw = _state
    if (raw == null)
      Txn.Active // we encode active as null to make requireActive checks smaller
    else if (raw eq "merged")
      parUndo.status
    else if (raw.isInstanceOf[TxnLevelImpl])
      Txn.Active // child is active
    else
      raw.asInstanceOf[Txn.Status]
  }

  def setCommitting() {
    _state = Txn.Committing
  }

  def setCommitted() {
    _state = Txn.Committed
    notifyCompleted()
  }

  def tryActiveToCommitted(): Boolean = {
    val f = stateUpdater.compareAndSet(this, null, Txn.Committed)
    if (f)
      notifyCompleted()
    f
  }

  def tryActiveToPreparing(): Boolean = {
    val f = stateUpdater.compareAndSet(this, null, Txn.Preparing)
    if (f && txn.commitBarrier != null)
      notifyBlockedBarrierMembers()
    f
  }

  def tryPreparingToPrepared(): Boolean = stateUpdater.compareAndSet(this, Txn.Preparing, Txn.Prepared)

  def tryPreparingToCommitting(): Boolean = stateUpdater.compareAndSet(this, Txn.Preparing, Txn.Committing)

  /** Equivalent to `status` if this level is the current level, otherwise
   *  the result is undefined.
   */
  def statusAsCurrent: Txn.Status = {
    val raw = _state
    if (raw == null)
      Txn.Active
    else
      raw.asInstanceOf[Txn.Status]
  }

  private def notifyCompleted() {
    if (_waiters)
      synchronized { notifyAll() }
  }

  // We are looking for a chain of blockedBy txns that ends in a Prepared txn,
  // and the beginning and the end of the chain have the same non-null commit
  // barrier.  This is made a bit tricky because the deadlock chain might not
  // form from either end, some of the links might not be commit barrier
  // members, and one of the steps to building the chain might not be a call to
  // blockedBy.
  //
  // Our design places responsibility for checking on the beginning (Active) end
  // of the chain, and places responsibility for waking up threads that might
  // need to check on any thread that might complete a chain.

  @tailrec private def hasMemberCycle(cb: CommitBarrierImpl, src: TxnLevelImpl): Boolean = {
    if (src._state.isInstanceOf[Txn.RolledBack])
      false
    else {
      val next = src._blockedBy
      if (next == null)
        src.txn.commitBarrier == cb
      else
        hasMemberCycle(cb, next)
    }
  }

  private def isRolledBack: Boolean = _state.isInstanceOf[Txn.RolledBack]

  /** Blocks until `status.completed`, possibly returning early if `waiter`
   *  has been rolled back.
   */
  @throws(classOf[InterruptedException])
  def awaitCompleted(waiter: TxnLevelImpl, debugInfo: Any) {
    assert(parUndo == null)

    _waiters = true

    if (Stats.top != null)
      Stats.top.blockingAcquires += 1

    if (waiter != null) {
      val cb = waiter.txn.commitBarrier
      try {
        waiter._blockedBy = this
        notifyBlockedBarrierMembers()
        if (cb != null)
          addBlockedBarrierMember(waiter.txn, this)

        synchronized {
          if (!status.completed && !waiter.isRolledBack) {
            blocking {
              // We would not have to check that the waiter has been stolen from
              // except that when there is a commit barrier the thief might also be
              // the txn on which we are blocked
              while (!status.completed && !waiter.isRolledBack) {
                if (cb != null && hasMemberCycle(cb, waiter))
                  cb.cancelAll(CommitBarrier.MemberCycle(debugInfo))
                wait()
              }
            }
          }
        }

      } finally {
        if (cb != null)
          removeBlockedBarrierMember(waiter.txn)
        waiter._blockedBy = null
      }
    } else {
      synchronized {
        if (!status.completed)
          blocking { while (!status.completed) wait() }
      }
    }
  }


  def requireActive() {
    if (_state != null)
      slowRequireActive()
  }

  private def slowRequireActive() {
    status match {
      case Txn.RolledBack(_) => throw RollbackError
      case s => throw new IllegalStateException(s.toString)
    }
  }

  def pushIfActive(child: TxnLevelImpl): Boolean = {
    stateUpdater.compareAndSet(this, null, child)
  }

  def attemptMerge(): Boolean = {
    // First we need to set the current state to forwarding.  Regardless of
    // whether or not this fails we still need to unlink the parent.
    val f = (_state == null) && stateUpdater.compareAndSet(this, null, "merged")

    // We must use CAS to unlink ourselves from our parent, because we race
    // with remote cancels.
    if (parUndo._state eq this)
      stateUpdater.compareAndSet(parUndo, this, null)

    f
  }

  /** Must be called from the transaction's thread. */
  def forceRollback(cause: Txn.RollbackCause) {
    val s = rollbackImpl(Txn.RolledBack(cause))
    assert(s.isInstanceOf[Txn.RolledBack])
  }

  def requestRollback(cause: Txn.RollbackCause): Txn.Status = {
    if (cause.isInstanceOf[Txn.ExplicitRetryCause])
      throw new IllegalArgumentException("explicit retry is not available via requestRollback")
    rollbackImpl(Txn.RolledBack(cause))
  }

  // this is tailrec for retries, but not when we forward to child
  private def rollbackImpl(rb: Txn.RolledBack): Txn.Status = {
    val raw = _state
    if (raw == null || canAttemptLocalRollback(raw)) {
      // normal case
      if (stateUpdater.compareAndSet(this, raw, rb)) {
        notifyCompleted()
        rb
      } else
        rollbackImpl(rb) // retry
    } else if (raw eq "merged") {
      // we are now taking our status from our parent
      parUndo.rollbackImpl(rb)
    } else if (raw.isInstanceOf[TxnLevelImpl]) {
      // roll back the child first, then retry
      raw.asInstanceOf[TxnLevelImpl].rollbackImpl(rb)
      rollbackImpl(rb)
    } else {
      // request denied
      raw.asInstanceOf[Txn.Status]
    }
  }

  private def canAttemptLocalRollback(raw: AnyRef): Boolean = raw match {
    case Txn.Prepared => InTxnImpl.get eq txn // remote cancel is not allowed while preparing
    case s: Txn.Status => !s.decided
    case ch: TxnLevelImpl => ch.rolledBackOrMerged
    case _ => false
  }

  private def rolledBackOrMerged = _state match {
    case "merged" => true
    case Txn.RolledBack(_) => true
    case _ => false
  }
}
