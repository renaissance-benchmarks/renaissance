/* scala-stm - (c) 2009-2014, Stanford University, PPL */

package scala.concurrent.stm
package ccstm


private[ccstm] object InTxnImpl extends ThreadLocal[InTxnImpl] {

  override def initialValue = new InTxnImpl

  def apply()(implicit mt: MaybeTxn): InTxnImpl = mt match {
    case x: InTxnImpl => x
    case _ => get // this will create one
  }

  private def active(txn: InTxnImpl): InTxnImpl = if (txn.internalCurrentLevel != null) txn else null

  def dynCurrentOrNull: InTxnImpl = active(get)

  def currentOrNull(implicit mt: MaybeTxn) = active(apply())
}

private[stm] object RewindUnrecordedTxnError extends Error {
  override def fillInStackTrace(): Throwable = this
}

/** In CCSTM there is one `InTxnImpl` per thread, and it is reused across all
 *  transactions.
 *
 *  @author Nathan Bronson
 */
private[ccstm] class InTxnImpl extends InTxnRefOps {
  import CCSTM._
  import Txn._
  import skel.RollbackError

  //////////// pre-transaction state

  private var _alternatives: List[InTxn => Any] = Nil


  //////////// per-attempt history

  /** Subsumption dramatically reduces the overhead of nesting, but it doesn't
   *  allow partial rollback.  If we find out that partial rollback was needed
   *  then we disable subsumption and rerun the parent.
   */
  private var _subsumptionAllowed = true

  /** The total amount of modular blocking time performed on this thread since
   *  the last top-level commit or top-level permanent rollback.
   */
  private var _cumulativeBlockingNanos = 0L

  //////////////// per-transaction state

  /** A read will barge if `_barding && version(meta) >= _bargeVersion`. */
  protected var _barging: Boolean = false
  protected var _bargeVersion: Version = 0

  /** Non-negative values are assigned slots, negative values are the bitwise
   *  complement of the last used slot value.
   */
  protected var _slot: Slot = ~0

  private var _currentLevel: TxnLevelImpl = null

  private var _pendingFailure: Throwable = null

  /** This is the outer-most level that contains any subsumption, or null if
   *  there is no subsumption taking place.
   */
  private var _subsumptionParent: TxnLevelImpl = null

  /** Higher wins.  Currently priority doesn't change throughout the lifetime
   *  of a rootLevel.  It would be okay for it to monotonically increase, so
   *  long as there is no change of the current txn's priority between the
   *  priority check on conflict and any subsequent waiting that occurs.
   */
  private var _priority: Int = 0

  /** The read version of this transaction.  It is guaranteed that all values
   *  read by this transaction have a version number less than or equal to this
   *  value, and that any transaction whose writes conflict with this
   *  transaction will label those writes with a version number greater than
   *  this value.  The read version must never be greater than
   *  `globalVersion.get`, must never decrease, and each time it is
   *  changed the read set must be revalidated.  Lazily assigned.
   */
  private var _readVersion: Version = 0

  /** The commit barrier in which this transaction is participating. */
  var commitBarrier: CommitBarrierImpl = null

  //////////// value-like operations

  def status: Status = _currentLevel.statusAsCurrent

  def currentLevel: NestingLevel = {
    if (_subsumptionParent != null) {
      _subsumptionAllowed = false
      _subsumptionParent.forceRollback(OptimisticFailureCause('restart_to_materialize_current_level, None))
      throw RollbackError
    }
    _currentLevel
  }

  override def toString = {
    ("InTxnImpl@" + hashCode.toHexString + "(" +
            (if (_currentLevel == null) "Detached" else status.toString) +
            ", slot=" + _slot +
            ", subsumptionAllowed=" + _subsumptionAllowed +
            ", priority=" + _priority +
            ", readCount=" + readCount  +
            ", bargeCount=" + bargeCount +
            ", writeCount=" + writeCount +
            ", readVersion=0x" + _readVersion.toHexString +
            (if (_barging) ", bargingVersion=0x" + _bargeVersion.toHexString else "") +
            ", cumulativeBlockingNanos=" + _cumulativeBlockingNanos +
            ", commitBarrier=" + commitBarrier +
            ")")
  }


  //////////// methods for use by other CCSTM components

  protected def undoLog: TxnLevelImpl = _currentLevel

  protected def internalCurrentLevel: TxnLevelImpl = _currentLevel

  /** After this method returns, either the current transaction will have been
   *  rolled back, or it is safe to wait for `currentOwner` to be `Committed`
   *  or doomed.
   */
  def resolveWriteWriteConflict(owningRoot: TxnLevelImpl, contended: AnyRef) {
    // if write is not allowed, throw an exception of some sort
    requireActive()

    // TODO: boost our priority if we have written?

    // This test is _almost_ symmetric.  Tie goes to neither.
    if (this._priority <= owningRoot.txn._priority) {
      resolveAsWWLoser(owningRoot, contended, false, 'owner_has_priority)
    } else {
      // This will resolve the conflict regardless of whether it succeeds or fails.
      val s = owningRoot.requestRollback(OptimisticFailureCause('steal_by_higher_priority, Some(contended)))
      if (s == Preparing || s == Committing) {
        // owner can't be remotely canceled
        val msg = if (s == Preparing) 'owner_is_preparing else 'owner_is_committing
        resolveAsWWLoser(owningRoot, contended, true, msg)
      }
    }
  }

  private def resolveAsWWLoser(owningRoot: TxnLevelImpl, contended: AnyRef, ownerIsCommitting: Boolean, msg: Symbol) {
    if (!shouldWaitAsWWLoser(owningRoot, ownerIsCommitting)) {
      // The failed write is in the current nesting level, so we only need to
      // invalidate one nested atomic block.  Nothing will get better for us
      // until the current owner completes or this txn has a higher priority,
      // however.
      _currentLevel.forceRollback(OptimisticFailureCause(msg, Some(contended)))
      throw RollbackError
    }
  }

  private def shouldWaitAsWWLoser(owningRoot: TxnLevelImpl, ownerIsCommitting: Boolean): Boolean = {
    // If we haven't performed any writes or taken any pessimistic locks, there
    // is no point in not waiting.
    if (writeCount == 0 && bargeCount == 0 && !writeResourcesPresent)
      return true

    // If the current owner is in the process of committing then we should
    // wait, because we can't succeed until their commit is done.  This means
    // that regardless of priority all of this txn's retries are just useless
    // spins.  This is especially important in the case of external resources
    // that perform I/O during commit.  No deadlock is possible because a
    // committing txn already has all of the ownership it needs.
    if (ownerIsCommitting)
      return true

    // CommitBarrier-s have the ability to create priority inversion during
    // waiting, because a low-priority member can delay the completion of
    // the group even if the rest is composed of high-priority transactions
    // (or prepared transactions, that have infinite effective priority).
    // Although it seems tempting to try to add extra conditions under which
    // it is okay to wait, those conditions would need to hold during the
    // entire wait duration so they are not practical.
    if (commitBarrier != null)
      return false

    // We know that priority <= currentOwner.priority, because we're the loser.
    // If the priorities match exactly (unlikely but possible) then we can't
    // have both losers wait or we will get a deadlock.
    if (_priority == owningRoot.txn._priority)
      return false

    // Now we're in heuristic territory, waiting or rolling back are both
    // reasonable choices.  Waiting might reduce rollbacks, but it increases
    // the number of thread sleep/wakeup transitions, each of which is
    // expensive.  Our heuristic is to wait only if we are barging, which
    // indicates that we are having trouble making forward progress using
    // just blind optimism.  Also, since barging transactions prevent (some)
    // conflicting writes, this choice means we minimize the chance that a
    // doomed transaction blocks somebody that will be able to commit.
    return _barging
  }


  //////////// pre-txn state manipulation

  def pushAlternative(block: InTxn => Any): Boolean = {
    val z = _alternatives.isEmpty
    _alternatives ::= block
    z
  }

  private def takeAlternatives(): List[InTxn => Any] = {
    val z = _alternatives
    _alternatives = Nil
    z
  }


  //////////// high-level atomic block operations

  @throws(classOf[InterruptedException])
  protected[stm] def retry(): Nothing = {
    val timeout = _currentLevel.minEnclosingRetryTimeout()
    if (timeout == Long.MaxValue)
      rollback(ExplicitRetryCause(None))

    val consumed = _currentLevel.consumedRetryTotal()
    if (_cumulativeBlockingNanos < timeout + consumed)
      rollback(ExplicitRetryCause(Some(timeout + consumed)))

    _currentLevel.consumedRetryDelta += timeout
    throw new InterruptedException
  }

  @throws(classOf[InterruptedException])
  protected[stm] def retryFor(timeoutNanos: Long) {
    val effectiveTimeout = _currentLevel.minEnclosingRetryTimeout()
    if (effectiveTimeout < timeoutNanos)
      retry() // timeout imposed by TxnExecutor is tighter than this one

    val consumed = _currentLevel.consumedRetryTotal()
    if (_cumulativeBlockingNanos < timeoutNanos + consumed)
      rollback(ExplicitRetryCause(Some(timeoutNanos + consumed)))

    _currentLevel.consumedRetryDelta += timeoutNanos
  }

  @throws(classOf[InterruptedException])
  def atomic[Z](exec: TxnExecutor, block: InTxn => Z): Z = {
    if (!_alternatives.isEmpty)
      atomicWithAlternatives(exec, block)
    else {
      if (_currentLevel == null)
        topLevelAtomicImpl(exec, block)
      else
        nestedAtomicImpl(exec, block)
    }
  }

  @throws(classOf[InterruptedException])
  def atomicOneOf[Z](exec: TxnExecutor, blocks: Seq[InTxn => Z]): Z = {
    if (!_alternatives.isEmpty)
      throw new IllegalStateException("atomic.oneOf can't be mixed with orAtomic")
    val b = blocks.toList
    atomicImpl(exec, b.head, b.tail)
  }

  @throws(classOf[InterruptedException])
  def unrecorded[Z](exec: TxnExecutor, block: InTxn => Z, outerFailure: RollbackCause => Z): Z = {
    if (!_alternatives.isEmpty)
      throw new IllegalStateException("atomic.unrecorded can't be mixed with orAtomic")
    var z: Z = null.asInstanceOf[Z]
    try {
      atomicImpl(exec, { implicit txn =>
        z = block(txn)
        Txn.rollback(Txn.UnrecordedTxnCause(z))
      }, Nil)
    } catch {
      case RewindUnrecordedTxnError => z
      case RollbackError if outerFailure != null => {
        outerFailure(_currentLevel.statusAsCurrent.asInstanceOf[RolledBack].cause)
      }
    }
  }

  def rollback(cause: RollbackCause): Nothing = {
    // We need to grab the version numbers from writes and pessimistic reads
    // before the status is set to rollback, because as soon as the top-level
    // txn is marked rollback other threads can steal ownership.  This is
    // harmless if some other type of rollback occurs.
    if (isExplicitRetry(cause))
      addLatestWritesAsReads(_barging)

    _currentLevel.forceRollback(cause)
    throw RollbackError
  }


  //////////// per-block logic (includes reexecution loops)

  @throws(classOf[InterruptedException])
  private def awaitRetry(timeoutNanos: Long) {
    assert(_slot >= 0)
    val rs = takeRetrySet(_slot)
    detach()
    val f = _pendingFailure
    if (f != null) {
      _pendingFailure = null
      throw f
    }
    // Note that awaitRetry might throw an InterruptedException that cancels
    // the retry forever.
    val remaining = timeoutNanos - (if (timeoutNanos == Long.MaxValue) 0 else _cumulativeBlockingNanos)
    assert(remaining > 0)
    _cumulativeBlockingNanos += rs.awaitRetry(remaining)
  }

  private def isExplicitRetry(status: Status): Boolean = isExplicitRetry(status.asInstanceOf[RolledBack].cause)

  private def isExplicitRetry(cause: RollbackCause): Boolean = cause.isInstanceOf[ExplicitRetryCause]

  private def clearAttemptHistory() {
    _subsumptionAllowed = true
    _cumulativeBlockingNanos = 0L
    commitBarrier = null
  }

  //// nested, no alternatives

  private def nestedAtomicImpl[Z](exec: TxnExecutor, block: InTxn => Z): Z = {
    if (_subsumptionAllowed && (exec == _currentLevel.executor))
      subsumedNestedAtomicImpl(block)
    else
      trueNestedAtomicImpl(exec, block)
  }

  private def subsumedNestedAtomicImpl[Z](block: InTxn => Z): Z = {
    val outermost = _subsumptionParent == null
    if (outermost)
      _subsumptionParent = _currentLevel
    try {
      try {
        block(this)
      } catch {
        case x if x != RollbackError && !_currentLevel.executor.isControlFlow(x) => {
          // partial rollback is required, but we can't do it here
          _subsumptionAllowed = false
          _currentLevel.forceRollback(OptimisticFailureCause('restart_to_enable_partial_rollback, Some(x)))
          throw RollbackError
        }
      }
    } finally {
      if (outermost)
        _subsumptionParent = null
    }
  }

  private def trueNestedAtomicImpl[Z](exec: TxnExecutor, block: InTxn => Z): Z = {
    var prevFailures = 0
    (while (true) {
      // fail back to parent if it has been rolled back
      _currentLevel.requireActive()

      val level = new TxnLevelImpl(this, exec, _currentLevel, false)
      try {
        return nestedAttempt(prevFailures, level, block, -1)
      } catch {
        case RollbackError =>
      }
      // we are only here if it is a transient rollback or an explicit retry
      val cause = level.status.asInstanceOf[RolledBack].cause
      if (isExplicitRetry(cause)) {
        // Reads are still in access history.  Retry the parent, which will
        // treat the reads as its own.  The cause holds the timeout, if any.
        _currentLevel.forceRollback(cause)
        throw RollbackError
      }
      prevFailures += 1 // transient rollback, retry
    }).asInstanceOf[Nothing]
  }

  //// top-level, no alternatives

  @throws(classOf[InterruptedException])
  private def topLevelAtomicImpl[Z](exec: TxnExecutor, block: InTxn => Z): Z = {
    clearAttemptHistory()
    var prevFailures = 0
    (while (true) {
      var level = new TxnLevelImpl(this, exec, null, false)
      try {
        // successful attempt or permanent rollback either returns a Z or
        // throws an exception != RollbackError
        return topLevelAttempt(prevFailures, level, block)
      } catch {
        case RollbackError =>
      }
      // we are only here if it is a transient rollback or an explicit retry
      if (isExplicitRetry(level.status)) {
        val timeout = level.minRetryTimeoutNanos
        level = null // help the GC while waiting
        awaitRetry(timeout)
        prevFailures = 0
      } else {
        prevFailures += 1 // transient rollback, retry
      }
    }).asInstanceOf[Nothing]
  }

  //// nested or top-level, with alternatives

  @throws(classOf[InterruptedException])
  private def atomicWithAlternatives(exec: TxnExecutor, block: InTxn => Any): Nothing = {
    val z = atomicImpl(exec, block, takeAlternatives())
    throw new impl.AlternativeResult(z)
  }

  /** If parent level has status `RolledBack`, throws RollbackError.  On
   *  commit, returns a Z or throws an exception other than `RollbackError`.
   *  On permanent rollback, throws an exception other than `RollbackError`.
   *  On nested explicit retry, throws `RollbackError` and sets the parent
   *  level's status to `RolledBack(ExplicitRetryCause(_))`.  All other cases
   *  result in a retry within the method.
   */
  @throws(classOf[InterruptedException])
  private def atomicImpl[Z](exec: TxnExecutor, block: InTxn => Z, alternatives: List[InTxn => Z]): Z = {
    if (Stats.top != null)
      recordAlternatives(alternatives)

    if (_currentLevel == null)
      clearAttemptHistory()

    var reusedReadThreshold = -1
    var minRetryTimeout = Long.MaxValue
    (while (true) {
      var level: TxnLevelImpl = null
      var prevFailures = 0
      while (level == null) {
        // fail back to parent if it has been rolled back
        if (_currentLevel != null)
          _currentLevel.requireActive()

        // phantom attempts reuse reads from the previous one
        val phantom = reusedReadThreshold >= 0
        level = new TxnLevelImpl(this, exec, _currentLevel, phantom)
        level.minRetryTimeoutNanos = minRetryTimeout
        try {
          // successful attempt or permanent rollback either returns a Z or
          // throws an exception != RollbackError
          val b = if (phantom) { (_: InTxn) => atomicImpl(exec, alternatives.head, alternatives.tail) } else block
          if (_currentLevel != null)
            return nestedAttempt(prevFailures, level, b, reusedReadThreshold)
          else
            return topLevelAttempt(prevFailures, level, b)
        } catch {
          case RollbackError =>
        }
        // we are only here if it is a transient rollback or an explicit retry
        if (!isExplicitRetry(level.status)) {
          // transient rollback, retry (not as a phantom)
          prevFailures += 1
          reusedReadThreshold = -1
          level = null
        }
        // else explicit retry, exit the loop
      }

      // The attempt ended in an explicit retry.  If there are alternatives
      // then we run a phantom attempt that reuses the read from the last real
      // attempt on the block.  Phantom attempts can also end in explicit retry
      // (if all of the alternatives triggered retry), in which case we treat
      // them the same as a regular block with no alternatives.
      val phantom = reusedReadThreshold >= 0
      minRetryTimeout = level.minRetryTimeoutNanos
      if (!phantom && !alternatives.isEmpty) {
        // rerun a phantom
        reusedReadThreshold = level.prevReadCount
      } else {
        level = null

        // no more alternatives, reads are still in access history
        if (_currentLevel != null) {
          // retry the parent, which will treat the reads as its own
          _currentLevel.forceRollback(ExplicitRetryCause(None))
          throw RollbackError
        }

        // top-level retry after waiting for something to change
        awaitRetry(minRetryTimeout)
        minRetryTimeout = Long.MaxValue

        // rerun the real block, now that the await has completed
        reusedReadThreshold = -1
      }
    }).asInstanceOf[Nothing]
  }

  private def recordAlternatives(alternatives: List[_]) {
    (if (_currentLevel == null) Stats.top else Stats.nested).alternatives += alternatives.size
  }

  //////////// per-attempt logic

  /** On commit, either returns a Z or throws the control-flow exception from
   *  the committed attempted; on rollback, throws an exception on a permanent
   *  rollback or `RollbackError` on a transient rollback.
   */
  private def nestedAttempt[Z](prevFailures: Int, level: TxnLevelImpl, block: InTxn => Z, reusedReadThreshold: Int): Z = {
    nestedBegin(level, reusedReadThreshold)
    checkBarging(prevFailures)
    try {
      runBlock(block)
    } finally {
      rethrowFromStatus(nestedComplete())
    }
  }

  @throws(classOf[InterruptedException])
  private def topLevelAttempt[Z](prevFailures: Int, level: TxnLevelImpl, block: InTxn => Z): Z = {
    topLevelBegin(level)
    checkBarging(prevFailures)
    try {
      runBlock(block)
    } finally {
      rethrowFromStatus(topLevelComplete())
    }
  }

  private def checkBarging(prevFailures: Int) {
    // once we start barging we will use the original read version
    if (prevFailures == 0)
      _bargeVersion = _readVersion

    if (prevFailures == BargeAllThreshold)
      _bargeVersion = 0L

    _barging = prevFailures >= BargeRecentThreshold
  }

  private def nestedBegin(child: TxnLevelImpl, reusedReadThreshold: Int) {
    // link to child races with remote rollback. pushIfActive detects the race
    // and returns false
    if (!_currentLevel.pushIfActive(child)) {
      child.forceRollback(this.status.asInstanceOf[RolledBack].cause)
      throw RollbackError
    }

    // successfully begun
    _currentLevel = child
    checkpointCallbacks()
    checkpointAccessHistory(reusedReadThreshold)
  }

  @throws(classOf[InterruptedException])
  private def topLevelBegin(child: TxnLevelImpl) {
    if (_slot < 0) {
      _priority = skel.SimpleRandom.nextInt()
      _slot = slotManager.assign(child, ~_slot)
      _readVersion = freshReadVersion
    }
    // else we must be a top-level alternative
    _currentLevel = child
  }

  private def runBlock[Z](block: InTxn => Z): Z = {
    try {
      block(this)
    } catch {
      case x if x != RollbackError && !_currentLevel.executor.isControlFlow(x) => {
        _currentLevel.forceRollback(UncaughtExceptionCause(x))
        null.asInstanceOf[Z]
      }
    }
  }

  private def rethrowFromStatus(status: Status) {
    status match {
      case rb: RolledBack => {
        rb.cause match {
          case UncaughtExceptionCause(x) => throw x
          case _: UnrecordedTxnCause[_] => throw RewindUnrecordedTxnError
          case _: TransientRollbackCause => throw RollbackError
        }
      }
      case _ =>
    }
  }

  //////////// completion

  private def nestedComplete(): Status = {
    val child = _currentLevel
    if (child.attemptMerge()) {
      // child was successfully merged
      mergeAccessHistory()
      _currentLevel = child.parUndo
      Committed
    } else {
      val s = this.status

      // callbacks must be last, because they might throw an exception
      rollbackAccessHistory(_slot, s.asInstanceOf[RolledBack].cause)
      val handlers = rollbackCallbacks()
      _currentLevel = child.parUndo
      if (handlers != null)
        fireAfterCompletionAndThrow(handlers, child.executor, s, null)
      s
    }
  }

  //// top-level completion

  private def topLevelComplete(): Status = {
    if (attemptTopLevelComplete()) {
      finishTopLevelCommit()
      Committed
    } else {
      val s = this.status
      val c = s.asInstanceOf[RolledBack].cause
      if (isExplicitRetry(c))
        finishTopLevelRetry(s, c)
      else
        finishTopLevelRollback(s, c)
      s
    }
  }

  private def finishTopLevelCommit() {
    resetAccessHistory()
    val handlers = resetCallbacks()
    val exec = _currentLevel.executor
    detach()

    val f = _pendingFailure
    _pendingFailure = null
    fireAfterCompletionAndThrow(handlers, exec, Committed, f)
  }

  private def finishTopLevelRollback(s: Status, c: RollbackCause) {
    rollbackAccessHistory(_slot, c)
    val handlers = rollbackCallbacks()
    val exec = _currentLevel.executor
    detach()

    val f = _pendingFailure
    _pendingFailure = null
    fireAfterCompletionAndThrow(handlers, exec, s, f)
  }

  private def finishTopLevelRetry(s: Status, c: RollbackCause) {
    rollbackAccessHistory(_slot, c)
    val handlers = rollbackCallbacks()

    // don't detach, but we do need to give up the current level
    val exec = _currentLevel.executor
    _currentLevel = null
    assert(writeCount == 0)

    if (handlers != null)
      _pendingFailure = fireAfterCompletion(handlers, exec, s, _pendingFailure)

    if (_pendingFailure != null) {
      // scuttle the retry
      takeRetrySet(_slot)
      val f = _pendingFailure
      _pendingFailure = null
      throw f
    }
  }

  private def detach() {
    //assert(_slot >= 0 && readCount == 0 && bargeCount == 0 && writeCount == 0)
    slotManager.release(_slot)
    _slot = ~_slot
    _currentLevel = null
  }

  private def attemptTopLevelComplete(): Boolean = {
    val root = _currentLevel

    fireBeforeCommitCallbacks()

    // Read-only transactions are easy to commit, because all of the reads
    // are already guaranteed to be consistent.  We still have to release the
    // barging locks, though.
    if (writeCount == 0 && !writeResourcesPresent) {
      if (bargeCount > 0)
        releaseBargeLocks()
      return root.tryActiveToCommitted()
    }

    if (!root.tryActiveToPreparing() || !acquireLocks())
      return false

    // this is our linearization point
    val cv = freshCommitVersion(_readVersion)

    // if the reads are still valid, then they were valid at the linearization
    // point
    if (!revalidateImpl())
      return false

    fireWhilePreparingCallbacks()

    if (externalDecider != null) {
      // external decider doesn't have to content with cancel by other threads
      if (!root.tryPreparingToPrepared() || !consultExternalDecider())
        return false

      root.setCommitting()
    } else {
      // attempt to decide commit
      if (!root.tryPreparingToCommitting())
        return false
    }

    _pendingFailure = fireWhileCommittingCallbacks(_currentLevel.executor)
    commitWrites(cv)
    root.setCommitted()

    return true
  }

  private def releaseBargeLocks() {
    var i = bargeCount - 1
    while (i >= 0) {
      rollbackHandle(bargeHandle(i), _slot)
      i -= 1
    }
  }

  private def acquireLocks(): Boolean = {
    var i = writeCount - 1
    while (i >= 0) {
      // acquireLock is inlined to reduce the call depth from TxnExecutor.apply
      val handle = getWriteHandle(i)
      var m = 0L
      do {
        m = handle.meta
        if (owner(m) != _slot && m != txnLocalMeta)
          return false
        // we have to use CAS to guard against remote steal
      } while (!changing(m) && !handle.metaCAS(m, withChanging(m)))
      i -= 1
    }
    return true
  }

  private def consultExternalDecider(): Boolean = {
    try {
      if (!externalDecider.shouldCommit(this))
        _currentLevel.forceRollback(OptimisticFailureCause('external_decision, None))
    } catch {
      case x: Throwable => _currentLevel.forceRollback(UncaughtExceptionCause(x))
    }
    this.status eq Prepared
  }

  private def commitWrites(cv: Long) {
    var wakeups = 0L
    var i = writeCount - 1
    while (i >= 0) {
      val handle = getWriteHandle(i).asInstanceOf[Handle[Any]]

      val m = handle.meta
      if (pendingWakeups(m))
        wakeups |= wakeupManager.prepareToTrigger(handle)

      //assert(owner(m) == _slot)

      val v = getWriteSpecValue[Any](i)

      // release the lock, clear the PW bit, and update the version, but only
      // if this was the entry that actually acquired ownership
      if (wasWriteFreshOwner(i)) {
        // putting the data store in both sides allows the volatile writes to
        // be coalesced
        handle.data = v
        handle.meta = withCommit(m, cv)
      } else {
        handle.data = v
      }

      // because we release when we find the original owner, it is important
      // that we traverse in reverse order.  There are no duplicates
      i -= 1
    }

    // We still have ownership (but not exclusive) for pessimistic reads, and
    // we still have exclusive ownership of pessimistic reads that turned into
    // writes (or that share metadata with writes).  We rollback the vlock for
    // the former and commit the vlock for the later.
    i = bargeCount - 1
    while (i >= 0) {
      val handle = bargeHandle(i)
      val m = handle.meta

      if (changing(m)) {
        // a handle sharing this base and metaOffset must also be present in
        // the write buffer, so we should bump the version number
        handle.meta = withCommit(m, cv)
      } else {
        // this was only a pessimistic read, no need to bump the version
        rollbackHandle(handle, _slot, m)
      }

      i -= 1
    }

    // unblock anybody waiting on a value change
    if (wakeups != 0L)
      wakeupManager.trigger(wakeups)
  }

  //////////// validation

  /** Returns true if valid. */
  private def revalidateImpl(): Boolean = {
    // we check the oldest reads first, so that we roll back all intervening
    // invalid nesting levels
    var i = 0
    while (i < readCount) {
      val h = readHandle(i)
      val problem = checkRead(h, readVersion(i))
      if (problem != null) {
        readLocate(i).asInstanceOf[NestingLevel].requestRollback(OptimisticFailureCause(problem, Some(h)))
        return false
      }
      i += 1
    }
    fireWhileValidating()

    !this.status.isInstanceOf[RolledBack]
  }

  /** Returns the name of the problem on failure, null on success. */
  private def checkRead(handle: Handle[_], ver: CCSTM.Version): Symbol = {
    (while (true) {
      val m1 = handle.meta
      if (!changing(m1) || owner(m1) == _slot) {
        if (version(m1) != ver)
          return 'stale_read
        // okay
        return null
      } else if (owner(m1) == nonTxnSlot) {
        // non-txn updates don't set changing unless they will install a new
        // value, so we are the only party that can yield
        return 'read_vs_nontxn_write
      } else {
        // Either this txn or the owning txn must roll back.  We choose to
        // give precedence to the owning txn, as it is the writer and is
        // trying to commit.  There's a bit of trickiness since o may not be
        // the owning transaction, it may be a new txn that reused the same
        // slot.  If the actual owning txn committed then the version
        // number will have changed, which we will detect on the next pass
        // (because we aren't incrementing i, so we will revisit this
        // entry).  If it rolled back then we don't have to roll back, so
        // looking at o to make the decision doesn't affect correctness
        // (although it might result in an unnecessary rollback).  If the
        // owner slot is the same but the changing bit is not set (or if
        // the owner txn is null) then we are definitely observing a reused
        // slot and we can avoid the spurious rollback.
        val o = slotManager.lookup(owner(m1))
        if (null != o) {
          val s = o.status
          val m2 = handle.meta
          if (changing(m2) && owner(m2) == owner(m1)) {
            if (!s.isInstanceOf[RolledBack])
              return 'read_vs_pending_commit

            stealHandle(handle, m2, o)
          }
        }
      }
      // try again
    }).asInstanceOf[Nothing]
  }


  //////////// implementations of InTnRefOps abstract operations

  override def requireActive() {
    val cur = _currentLevel
    if (cur == null)
      throw new IllegalStateException("no active transaction")
    cur.requireActive()
  }

  protected def isNewerThanReadVersion(version: Version): Boolean = version > _readVersion

  /** On return, the read version will have been the global version at some
   *  point during the call, the read version will be >= minReadVersion, and
   *  all reads will have been validated against the new read version.  Throws
   *  `RollbackError` if invalid.
   */
  protected def revalidate(minReadVersion: Version) {
    _readVersion = freshReadVersion(minReadVersion)
    if (!revalidateImpl())
      throw RollbackError
  }

  protected def forceRollback(cause: RollbackCause) {
    _currentLevel.forceRollback(cause)
  }

  @throws(classOf[InterruptedException])
  protected def weakAwaitUnowned(handle: Handle[_], m0: Meta) {
    CCSTM.weakAwaitUnowned(handle, m0, _currentLevel)
  }
}
