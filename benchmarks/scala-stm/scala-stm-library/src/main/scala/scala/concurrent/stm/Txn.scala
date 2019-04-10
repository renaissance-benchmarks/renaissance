/* scala-stm - (c) 2009-2012, Stanford University, PPL */

package scala.concurrent.stm

import java.util.concurrent.TimeUnit

/** The `Txn` object provides methods that operate on the current transaction
 *  context.  These methods are only valid within an atomic block or a
 *  transaction life-cycle handler, which is checked at compile time by
 *  requiring that an implicit `InTxn` or `InTxnEnd` be available.
 *
 *  @author Nathan Bronson
 */
object Txn {
  import impl.STMImpl

  //////////// dynamic InTxn binding

  /** Returns `Some(t)` if called from inside the static or dynamic scope of
   *  the transaction context `t`, `None` otherwise.  If an implicit `InTxn` is
   *  available it may be used.
   */
  def findCurrent(implicit mt: MaybeTxn): Option[InTxn] = STMImpl.instance.findCurrent


  //////////// status

  /** The current state of an attempt to execute an atomic block. */
  sealed abstract class Status {

    /** True for `Committing`, `Committed` and `RolledBack`. */
    def decided: Boolean

    /** True for `Committed` and `RolledBack`. */
    def completed: Boolean
  }

  /** The `Status` for a transaction nesting level that may perform `Ref` reads
   *  and writes, that is waiting for a child nesting level to complete, or
   *  that has been merged into an `Active` parent nesting level.
   */
  case object Active extends Status {
    def decided = false
    def completed = false
  }

  /** The `Status` for the nesting levels of a transaction that are attempting
   *  to commit, but for which the outcome is uncertain.
   */
  case object Preparing extends Status {
    def decided = false
    def completed = false
  }

  /** The `Status` for the nesting levels of a transaction that has
   *  successfully acquired all write permissions necessary to succeed, and
   *  that has delegated the final commit decision to an external decider.
   */
  case object Prepared extends Status {
    def decided = false
    def completed = false
  }

  /** The `Status` for the nesting levels of a transaction that has decided to 
   *  commit, but whose `Ref` writes are not yet visible to other threads.
   */
  case object Committing extends Status {
    def decided = true
    def completed = false
  }

  /** The `Status` for the nesting levels of a transaction that has been
   *  committed.  After-commit callbacks may still be running.
   */
  case object Committed extends Status {
    def decided = true
    def completed = true
  }

  /** The `Status` for an atomic block execution attempt that is being or that
   *  has been cancelled.  None of the `Ref` writes made during this nesting
   *  level or in any child nesting level will ever be visible to other
   *  threads.  The atomic block will be automatically retried if `cause` is a
   *  `TransientRollbackCause`, unless STM-specific retry thresholds are
   *  exceeded.
   */
  case class RolledBack(cause: RollbackCause) extends Status {
    def decided = true
    def completed = true
  }


  /** A record of the reason that a atomic block execution attempt was rolled
   *  back.
   */
  sealed abstract class RollbackCause

  /** `RollbackCause`s for which the failure is transient and another attempt
   *  should be made to execute the underlying atomic block.
   */
  sealed abstract class TransientRollbackCause extends RollbackCause

  /** `RollbackCause`s for which the failure is permanent and no attempt should
   *  be made to retry the underlying atomic block.
   */
  sealed abstract class PermanentRollbackCause extends RollbackCause

  /** The `RollbackCause` for a `NestingLevel` whose optimistic execution was
   *  invalid, and that should be retried.  The specific situations in which an
   *  optimistic failure can occur are specific to the STM algorithm, but may
   *  include:
   *  - the STM detected that the value returned by a previous read in this
   *    nesting level is no longer valid;
   *  - a cyclic dependency has occurred and this nesting level must be rolled
   *    back to avoid deadlock;
   *  - a transaction with a higher priority wanted to write to a `Ref` written
   *    by this transaction;
   *  - the STM decided to switch execution strategies for this atomic block;
   *    or
   *  - no apparent reason (*).
   *
   *  (*) - Some STMs perform validation, conflict detection and deadlock cycle
   *  breaking using algorithms that are conservative approximations.  This
   *  means that any particular attempt to execute an atomic block might fail
   *  spuriously.
   *
   *  @param category an STM-specific label for the reason behind this
   *                  optimistic failure. The set of possible categories is
   *                  bounded.
   *  @param trigger  the specific object that led to the optimistic failure,
   *                  if it is available, otherwise `None`.
   */
  case class OptimisticFailureCause(category: Symbol, trigger: Option[Any]) extends TransientRollbackCause

  /** The `RollbackCause` for an atomic block execution attempt that ended with
   *  a call to `retry` or `retryFor`.  The atomic block will be retried after
   *  some memory location read in the previous attempt has changed.
   */
  case class ExplicitRetryCause(timeoutNanos: Option[Long]) extends TransientRollbackCause

  /** The `RollbackCause` for an atomic block that should not be restarted
   *  because it threw an exception.  The exception might have been thrown from
   *  the body of the atomic block or from a handler invoked before the commit
   *  decision.  Exceptions used for control flow are not included (see
   *  `TxnExecutor.isControlFlow`).
   *
   *  Scala's STM discards `Ref` writes performed by atomic blocks that throw
   *  an exception.  This is referred to as "failure atomicity".  In a system
   *  that uses exceptions for error cleanup this design tends to preserve the
   *  invariants of shared data structures, which is a good thing.  If a system
   *  uses exceptions for control flow, however, this design may lead to
   *  unexpected behavior.  The `TxnExecutor` object's `isControlFlow` method
   *  is used to distinguish exceptions representing control flow transfers
   *  from those used to represent error conditions.  See
   *  `TxnExecutor.transformDefault` to change the default rules.
   */
  case class UncaughtExceptionCause(x: Throwable) extends PermanentRollbackCause

  /** The `RollbackCause` of a successfully completed `atomic.unrecorded`
   *  block.  See `TxnExecutor.unrecorded`.
   */
  case class UnrecordedTxnCause[Z](z: Z) extends PermanentRollbackCause

  /** Returns the status of the current nesting level of the current
   *  transaction, equivalent to `NestingLevel.current.status`.
   */
  def status(implicit txn: InTxnEnd): Status = txn.status


  //////////// explicit retry and rollback

  // These are methods of the Txn object because it is generally only correct
  // to call them inside the static context of an atomic block.  If they were
  // methods on the InTxn instance, then users might expect to be able to call
  // them from any thread.  Methods to add life-cycle callbacks are also object
  // methods for the same reason.

  /** Rolls back the current nesting level for modular blocking.  It will be
   *  retried, but only after some memory location observed by this transaction
   *  has been changed.  If any alternatives to this atomic block were provided
   *  via `orAtomic` or `atomic.oneOf`, then the alternative will be tried
   *  before blocking.
   *  @throws IllegalStateException if the transaction is not active.
   */
  def retry(implicit txn: InTxn): Nothing = txn.retry()

  /** Causes the transaction to roll back and retry using modular blocking with
   *  a timeout, or returns immediately if the timeout has already expired.
   *  The STM keeps track of the total amount of blocking that has occurred
   *  during modular blocking; this time is apportioned among the calls to
   *  `View.tryAwait` and `retryFor` that are part of the current attempt.
   *  `retryFor(0)` is a no-op.
   *
   *  Returns only if the timeout has expired.
   *  @param timeout the maximum amount of time that this `retryFor` should
   *      block, in units of `unit`.
   *  @param unit the units in which to measure `timeout`, by default
   *      milliseconds.
   */
  def retryFor(timeout: Long, unit: TimeUnit = TimeUnit.MILLISECONDS)(implicit txn: InTxn) {
    txn.retryFor(unit.toNanos(timeout))
  }

  /** Causes the current nesting level to be rolled back due to the specified
   *  `cause`.  This method may only be called by the thread executing the
   *  transaction; obtain a `NestingLevel` instance `n` and call
   *  `n.requestRollback(cause)` if you wish to doom a transaction from another
   *  thread.
   *  @throws IllegalStateException if the current transaction has already
   *      decided to commit.
   */
  def rollback(cause: RollbackCause)(implicit txn: InTxnEnd): Nothing = txn.rollback(cause)


  //////////// life-cycle callbacks

  /** Arranges for `handler` to be executed as late as possible while the root
   *  nesting level of the current transaction is still `Active`, unless the
   *  current nesting level is rolled back.  Reads, writes and additional
   *  nested transactions may be performed inside the handler.  Details:
   *  - it is possible that after `handler` is run the transaction might still
   *    be rolled back;
   *  - it is okay to call `beforeCommit` from inside `handler`, the
   *    reentrantly added handler will be included in this before-commit phase;
   *    and
   *  - before-commit handlers will be executed in their registration order.
   */
  def beforeCommit(handler: InTxn => Unit)(implicit txn: InTxn) { txn.beforeCommit(handler) }

  /** (rare) Arranges for `handler` to be called after the `Ref` reads and
   *  writes have been checked for serializability, but before the decision has
   *  been made to commit or roll back.  While-preparing handlers can lead to
   *  scalability problems, because while this transaction is in the
   *  `Preparing` state it might obstruct other transactions.  Details:
   *  - the handler must not access any `Ref`s, even using `Ref.single`;
   *  - handlers will be executed in their registration order; and
   *  - handlers may be registered while the transaction is active, or from a
   *    while-preparing callback during the `Preparing` phase.
   */
  def whilePreparing(handler: InTxnEnd => Unit)(implicit txn: InTxnEnd) { txn.whilePreparing(handler) }

  /** (rare) Arranges for `handler` to be called after (if) it has been decided
   *  that the current transaction will commit, but before the writes made by
   *  the transaction have become available to other threads.  While-committing
   *  handlers can lead to scalability problems, because while this transaction
   *  is in the `Committing` state it might obstruct other transactions.
   *  Details:
   *  - the handler must not access any `Ref`s, even using `Ref.single`;
   *  - handlers will be executed in their registration order; and
   *  - handlers may be registered so long as the current transaction status is
   *    not `RolledBack` or `Committed`.
   */
  def whileCommitting(handler: InTxnEnd => Unit)(implicit txn: InTxnEnd) { txn.whileCommitting(handler) }

  /** Arranges for `handler` to be executed as soon as possible after the
   *  current transaction is committed, if this nesting level is part of the
   *  overall transaction commit.  Details:
   *  - no transaction will be active while the handler is run, but it may
   *    access `Ref`s using a new top-level atomic block or `.single`;
   *  - the handler runs after all internal locks have been released, so any
   *    values read or written in the transaction might already have been
   *    changed by another thread before the handler is executed;
   *  - handlers will be executed in their registration order; and
   *  - handlers may be registered so long as the current transaction status is
   *    not `RolledBack` or `Committed`.
   */
  def afterCommit(handler: Status => Unit)(implicit txn: InTxnEnd) { txn.afterCommit(handler) }

  /** Arranges for `handler` to be executed as soon as possible after the
   *  current nesting level is rolled back, or runs the handler immediately if
   *  the current nesting level's status is already `RolledBack`.  Details:
   *  - the handler will be executed during any partial rollback that includes
   *    the current nesting level;
   *  - the handler will be run before any additional attempts to execute the
   *    atomic block;
   *  - handlers will be run in the reverse of their registration order; and
   *  - handlers may be registered so long as the current transaction status is
   *    not `Committed`.
   */
  def afterRollback(handler: Status => Unit)(implicit txn: InTxnEnd) { txn.afterRollback(handler) }

  /** Arranges for `handler` to be called as both an after-commit and
   *  after-rollback handler.
   *
   *  Equivalent to: {{{
   *     afterRollback(handler)
   *     afterCommit(handler)
   *  }}}
   */
  def afterCompletion(handler: Status => Unit)(implicit txn: InTxnEnd) { txn.afterCompletion(handler) }


  /** An `ExternalDecider` is given the final control over the decision of
   *  whether or not to commit a transaction, which allows two-phase commit to
   *  be integrated with a single non-transactional resource.  `shouldCommit`
   *  will only be called if a `InTxn` has successfully called all of its
   *  before-commit handlers, acquired all necessary write locks, validated all
   *  of its reads and called all of its while-preparing handlers.  The decider
   *  may then attempt a non-transactional operation whose outcome is
   *  uncertain, and based on the outcome may directly cause the transaction to
   *  commit or roll back.
   */
  trait ExternalDecider {
    /** Should return true if the end-of-life transaction `txn` should commit,
     *  false if it should roll back.  `Txn.rollback` may also be used to
     *  initiate a rollback if that is more convenient.  Called while the
     *  status is `Prepared`.  This method may not access any `Ref`s, even via
     *  `Ref.single`.
     */
    def shouldCommit(implicit txn: InTxnEnd): Boolean
  }

  /** (rare) Delegates final decision of the outcome of the transaction to
   *  `decider` if the current nesting level participates in the top-level
   *  commit.  This method can succeed with at most one value per top-level
   *  transaction.
   *  @throws IllegalStateException if the current transaction's status is not
   *      `Active` or `Preparing`
   *  @throws IllegalArgumentException if `setExternalDecider(d)` was
   *      previously called in this transaction, `d != decider`, and the
   *      nesting level from which `setExternalDecider(d)` was called has not
   *      rolled back.
   */
  def setExternalDecider(decider: ExternalDecider)(implicit txn: InTxnEnd) { txn.setExternalDecider(decider) }
}
