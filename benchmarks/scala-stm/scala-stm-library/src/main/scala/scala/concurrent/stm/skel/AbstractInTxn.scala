/* scala-stm - (c) 2009-2012, Stanford University, PPL */

package scala.concurrent.stm
package skel

import annotation.tailrec

private[stm] trait AbstractInTxn extends InTxn {
  import Txn._

  /** This is different from `currentLevel` so that `InTxn` instances can
   *  assume that the return value from `topLevel` is not exposed to the user.
   */
  protected def internalCurrentLevel: AbstractNestingLevel

  //////////// implementation of functionality for the InTxn implementer

  protected def requireActive() {
    internalCurrentLevel.status match {
      case Active =>
      case RolledBack(_) => throw RollbackError
      case s => throw new IllegalStateException(s.toString)
    }
  }

  protected def requireNotDecided() {
    internalCurrentLevel.status match {
      case s if !s.decided =>
      case RolledBack(_) => throw RollbackError
      case s => throw new IllegalStateException(s.toString)
    }
  }

  protected def requireNotCompleted() {
    internalCurrentLevel.status match {
      case s if !s.completed =>
      case RolledBack(_) => throw RollbackError
      case s => throw new IllegalStateException(s.toString)
    }
  }

  private var _decider: ExternalDecider = null
  protected def externalDecider = _decider

  /** Set to true if any callbacks are registered. */
  private var _callbacksPresent = false
  
  private val _beforeCommitList = new CallbackList[InTxn]
  private val _whileValidatingList = new CallbackList[NestingLevel]
  private val _whilePreparingList = new CallbackList[InTxnEnd]
  private val _whileCommittingList = new CallbackList[InTxnEnd]
  private val _afterCommitList = new CallbackList[Status]
  private val _afterRollbackList = new CallbackList[Status]

  /** Returns true if there are while-preparing handlers, while-committing
   *  handlers, or an external decider.
   */
  protected def writeResourcesPresent: Boolean = _callbacksPresent && writeResourcesPresentImpl

  private def writeResourcesPresentImpl: Boolean = {
    !_whilePreparingList.isEmpty || !_whileCommittingList.isEmpty || externalDecider != null
  }

  protected def fireBeforeCommitCallbacks() {
    if (_callbacksPresent)
      _beforeCommitList.fire(internalCurrentLevel, this)
  }

  protected def fireWhilePreparingCallbacks() {
    if (_callbacksPresent && !_whilePreparingList.isEmpty)
      _whilePreparingList.fire(internalCurrentLevel, this)
  }

  protected def fireWhileCommittingCallbacks(exec: TxnExecutor): Throwable = {
    if (_callbacksPresent && !_whileCommittingList.isEmpty)
      fireWhileCommittingCallbacksImpl(exec)
    else
      null
  }

  private def fireWhileCommittingCallbacksImpl(exec: TxnExecutor): Throwable = {
    var failure: Throwable = null
    var i = 0
    while (i < _whileCommittingList.size) {
      failure = firePostDecision(_whileCommittingList(i), this, exec, Txn.Committing, failure)
      i += 1
    }
    failure
  }

  protected def fireAfterCompletionAndThrow(handlers: Array[Status => Unit], exec: TxnExecutor, s: Status, pendingFailure: Throwable) {
    val f = if (handlers != null) fireAfterCompletion(handlers, exec, s, pendingFailure) else pendingFailure
    if (f != null)
      throw f
  }

  protected def fireAfterCompletion(handlers: Array[Status => Unit], exec: TxnExecutor, s: Status, f0: Throwable): Throwable = {
    var failure = f0
    var i = 0
    val inOrder = s eq Committed
    var j = if (inOrder) 0 else handlers.length - 1
    var dj = if (inOrder) 1 else -1
    while (i < handlers.length) {
      failure = firePostDecision(handlers(j), s, exec, s, failure)
      i += 1
      j += dj
    }
    failure
  }

  private def firePostDecision[A](handler: A => Unit, arg: A, exec: TxnExecutor, s: Status, f: Throwable): Throwable = {
    try {
      handler(arg)
      f
    } catch {
      case x: Throwable => {
        try {
          exec.postDecisionFailureHandler(s, x)
          f
        } catch {
          case xx: Throwable => xx
        }
      }
    }
  }

  protected def checkpointCallbacks() {
    if (_callbacksPresent)
      checkpointCallbacksImpl()
  }

  private def checkpointCallbacksImpl() {
    val level = internalCurrentLevel
    level._beforeCommitSize = _beforeCommitList.size
    level._whileValidatingSize = _whileValidatingList.size
    level._whilePreparingSize = _whilePreparingList.size
    level._whileCommittingSize = _whileCommittingList.size
    level._afterCommitSize = _afterCommitList.size
    level._afterRollbackSize = _afterRollbackList.size
  }

  /** Returns the discarded `afterRollbackList` entries, or null if none */
  protected def rollbackCallbacks(): Array[Status => Unit] = {
    if (!_callbacksPresent) null else rollbackCallbacksImpl()
  }

  private def rollbackCallbacksImpl(): Array[Status => Unit] = {
    val level = internalCurrentLevel
    _beforeCommitList.size = level._beforeCommitSize
    _whileValidatingList.size = level._whileValidatingSize
    _whilePreparingList.size = level._whilePreparingSize
    _whileCommittingList.size = level._whileCommittingSize
    _afterCommitList.size = level._afterCommitSize
    _afterRollbackList.truncate(level._afterRollbackSize)
  }

  /** Returns the discarded `afterCommitList` entries, or null if none. */
  protected def resetCallbacks(): Array[Status => Unit] = {
    if (!_callbacksPresent) null else resetCallbacksImpl()
  }

  private def resetCallbacksImpl(): Array[Status => Unit] = {
    _beforeCommitList.size = 0
    _whileValidatingList.size = 0
    _whilePreparingList.size = 0
    _whileCommittingList.size = 0
    _afterRollbackList.size = 0
    _afterCommitList.truncate(0)
  }

  protected def fireWhileValidating() {
    val n = _whileValidatingList.size
    if (n > 0)
      fireWhileValidating(n - 1, internalCurrentLevel)
  }

  @tailrec private def fireWhileValidating(i: Int, level: AbstractNestingLevel) {
    if (i >= 0) {
      if (i < level._whileValidatingSize)
        fireWhileValidating(i, level.parLevel)
      else if (level.status.isInstanceOf[Txn.RolledBack])
        fireWhileValidating(level._whileValidatingSize - 1, level.parLevel) // skip the rest at this level
      else {
        try {
          _whileValidatingList(i)(level)
        } catch {
          case x: Throwable => level.requestRollback(UncaughtExceptionCause(x))
        }
        fireWhileValidating(i - 1, level)
      }
    }
  }

  //////////// implementation of functionality for the InTxn user

  override def rootLevel: AbstractNestingLevel = internalCurrentLevel.root

  def beforeCommit(handler: InTxn => Unit) {
    requireActive()
    _callbacksPresent = true
    _beforeCommitList += handler
  }

  def whileValidating(handler: NestingLevel => Unit) {
    requireActive()
    _callbacksPresent = true
    _whileValidatingList += handler
  }

  def whilePreparing(handler: InTxnEnd => Unit) {
    requireNotDecided()
    _callbacksPresent = true
    _whilePreparingList += handler
  }

  def whileCommitting(handler: InTxnEnd => Unit) {
    requireNotCompleted()
    _callbacksPresent = true
    _whileCommittingList += handler
  }

  def afterCommit(handler: Status => Unit) {
    requireNotCompleted()
    _callbacksPresent = true
    _afterCommitList += handler
  }

  def afterRollback(handler: Status => Unit) {
    try {
      requireNotCompleted()
    } catch {
      case RollbackError => {
        handler(internalCurrentLevel.status)
        throw RollbackError
      }
    }
    _callbacksPresent = true
    _afterRollbackList += handler
  }

  def afterCompletion(handler: Status => Unit) {
    afterRollback(handler)
    _afterCommitList += handler
  }

  def setExternalDecider(decider: ExternalDecider) {
    if (status.decided)
      throw new IllegalArgumentException("can't set ExternalDecider after decision, status = " + status)

    if (_decider != null) {
      if (_decider != decider)
        throw new IllegalArgumentException("can't set two different ExternalDecider-s in the same top-level atomic block")
    } else {
      _decider = decider
      // the decider should be unregistered after either rollback or commit
      afterCompletion { status =>
        assert(_decider eq decider)
        _decider = null
      }
    }
  }
}
