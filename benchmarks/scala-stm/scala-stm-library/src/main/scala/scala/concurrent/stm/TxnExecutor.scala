/* scala-stm - (c) 2009-2012, Stanford University, PPL */

package scala.concurrent.stm

import java.util.concurrent.TimeUnit
import concurrent.stm.Txn.RollbackCause


/** `object TxnExecutor` manages the system-wide default `TxnExecutor`. */
object TxnExecutor {
  @volatile private var _default: TxnExecutor = impl.STMImpl.instance

  /** Returns the default `TxnExecutor`. */
  def defaultAtomic: TxnExecutor = _default

  /** Atomically replaces the default `TxnExecutor` with `f(defaultAtomic)`. */
  def transformDefault(f: TxnExecutor => TxnExecutor) {
    synchronized { _default = f(_default) }
  }

  val DefaultPostDecisionExceptionHandler = { (status: Txn.Status, x: Throwable) =>
    throw x
  }
}

/** A `TxnExecutor` is responsible for executing atomic blocks transactionally
 *  using a set of configuration parameters.  Configuration changes are made by
 *  constructing a new `TxnExecutor` using `withConfig` or `withHint`.  The
 *  new executor may be used immediately, saved and used multiple times, or
 *  registered as the new system-wide default using
 *  `TxnExecutor.transformDefault`.
 *
 *  @author Nathan Bronson
 */
trait TxnExecutor {

  //////// functionality

  /** Executes `block` one or more times until an atomic execution is achieved,
   *  buffering and/or locking writes so they are not visible until success.
   *
   *  @param    block code to execute atomically
   *  @tparam   Z the return type of the atomic block
   *  @return   the value returned from `block` after a successful optimistic
   *            concurrency attempt
   */
  def apply[Z](block: InTxn => Z)(implicit mt: MaybeTxn): Z

  /** Atomically executes a transaction that is composed from `blocks` by
   *  joining with a left-biased `orAtomic` operator.  The following two
   *  examples are equivalent.  Using `orAtomic`:
   *  {{{
   *    atomic { implicit t =>
   *      // body A
   *    } orAtomic { implicit t =>
   *      // body B
   *    } ...
   *  }}}
   *  Using `oneOf`:
   *  {{{
   *    atomic.oneOf( { implicit t: InTxn =>
   *      // body A
   *    }, { implicit t: InTxn =>
   *      // body B
   *    } )
   *  }}}
   *
   *  The first block will be attempted in an optimistic transaction until it
   *  either succeeds, fails with no retry possible (in which case the causing
   *  exception will be rethrown), or performs a call to `retry`.  If a retry
   *  is requested, then the next block will be attempted in the same fashion.
   *  If all blocks are explicitly retried then execution resumes at the first
   *  block, but only after another context has changed some value read by one
   *  of the attempts.
   *
   *  The left-biasing of the `orAtomic` composition guarantees that if the
   *  first block does not call `retry`, no other blocks will be executed.
   */
  def oneOf[Z](blocks: (InTxn => Z)*)(implicit mt: MaybeTxn): Z

  /** Performs a computation in a transaction and returns the result, but
   *  always rolls back the transaction.  No writes performed by `block` will
   *  be committed or exposed to other threads.  This may be useful for
   *  heuristic decisions or for debugging, as for the various `dbgStr`
   *  implementations.
   *
   *  '''The caller is responsible for correctness:''' It is a code smell
   *  if ''Z'' is a type that is constructed from Ref`, `TMap`, `TSet`, .....
   *
   *  If this method is executed inside an outer transaction that has status
   *  `Txn.RolledBack` then `block` can't complete.  The default behavior
   *  (if `outerFailure` is null) in that case is to immediately roll back
   *  the outer transaction.  If a non-null `outerFailure` handler has been
   *  provided, however, it allow this method to return.  This is useful when
   *  the unrecorded transaction is being used for debugging or logging.
   *
   *  `atomic.unrecorded { implicit txn => code }` is roughly equivalent to
   *  the following, except that the rollback cause used will be
   *  `Txn.UnrecordedTxnCause`: {{{
   *    case class Tunnel(z: Z) extends Exception {}
   *    try {
   *      atomic.withControlFlowRecognizer({
   *        case Tunnel(_) => false
   *      }) { implicit txn =>
   *        throw Tunnel(code)
   *      }
   *    } catch {
   *      case Tunnel(z) => z
   *    }
   *  }}}
   */
  def unrecorded[Z](block: InTxn => Z, outerFailure: (RollbackCause => Z) = null)(implicit mt: MaybeTxn): Z

  /** (rare) Associates an alternative atomic block with the current thread.
   *  The next call to `apply` will consider `block` to be an alternative.
   *  Multiple alternatives may be associated before calling `apply`.  Returns
   *  true if this is the first pushed alternative, false otherwise.  This
   *  method is not usually called directly.  Alternative atomic blocks are
   *  only attempted if the previous alternatives call `retry`.
   *
   *  Note that it is not required that `pushAlternative` be called on the same
   *  instance of `TxnExecutor` as `apply`, just that they have been derived
   *  from the same original executor.
   */
  def pushAlternative[Z](mt: MaybeTxn, block: InTxn => Z): Boolean
  
  /** Atomically compares and sets two `Ref`s, probably more efficiently then
   *  the corresponding transaction.  Equivalent to {{{
   *     atomic { implicit t =>
   *       a() == a0 && b() == b0 && { a() = a1 ; b() = b1 ; true }
   *     }
   *  }}}
   */
  def compareAndSet[A, B](a: Ref[A], a0: A, a1: A, b: Ref[B], b0: B, b1: B): Boolean

  /** Atomically compares and sets two `Ref`s using identity comparison,
   *  probably more efficiently then the corresponding transaction.  Equivalent
   *  to {{{
   *    atomic { implicit t =>
   *      val f = (a() eq a0) && (b() eq b0)
   *      if (f && (a0 ne a1))
   *        a() = a1
   *      if (f && (b0 ne b1))
   *        b() = b1
   *      f
   *    }
   *  }}}
   */
  def compareAndSetIdentity[A <: AnyRef, B <: AnyRef](a: Ref[A], a0: A, a1: A, b: Ref[B], b0: B, b1: B): Boolean

  //////// configuration

  /** Returns `Some(t)` if `t` is the retry timeout in nanoseconds used by
   *  this `TxnExecutor`, or `None` otherwise.  If the retry timeout is
   *  `Some(t)` and an atomic block executed by the returned executor blocks
   *  with `retry` or `retryFor` for more than `t` nanoseconds the retry will
   *  be cancelled with an `InterruptedException`.
   *
   *  The retry timeout has essentially the same effect as replacing calls to
   *  `retry` with
   *  `{ retryFor(timeout, NANOS) ; throw new InterruptedException }`.
   *  Alternately, `retryFor(timeout)` has roughly the same effect as {{{
   *    try {
   *      atomic.withRetryTimeout(timeout) { implicit txn => retry }
   *    } catch {
   *      case _: InterruptedException =>
   *    }
   *  }}}
   */
  def retryTimeoutNanos: Option[Long]

  /** Returns a `TxnExecutor` that is identical to this one, except that it has
   *  a `retryTimeout` of `timeoutNanos`.
   */
  def withRetryTimeoutNanos(timeoutNanos: Option[Long]): TxnExecutor

  /** Returns a `TxnExecutor` that is identical to this one except that it has
   *  the specified retry timeout.  The default time unit is milliseconds.  If
   *  the retry timeout expires the retry will be cancelled with an
   *  `InterruptedException`.
   */
  def withRetryTimeout(timeout: Long, unit: TimeUnit = TimeUnit.MILLISECONDS): TxnExecutor =
      withRetryTimeoutNanos(Some(unit.toNanos(timeout)))

  /** Returns true if `x` should be treated as a transfer of control, rather
   *  than an error.  Atomic blocks that end with an uncaught control flow
   *  exception are committed, while atomic blocks that end with an uncaught
   *  error exception are rolled back.
   *
   *  All implementations of this method must return true for instances that
   *  implement `scala.util.control.ControlThrowable`.
   */
  def isControlFlow(x: Throwable): Boolean

  /** Returns a `TxnExecutor e` that is identical to this one, except that
   *  `e.isControlFlow(x)` will return `pf(x)` if `pf.isDefined(x)`.  For
   *  exceptions for which `pf` is not defined the decision will be deferred to
   *  the previous implementation.
   *
   *  This function may be combined with `TxnExecutor.transformDefault` to add
   *  system-wide recognition of a control-transfer exception that does not
   *  extend `scala.util.control.ControlThrowable`.  For example, to modify the
   *  default behavior of all `TxnExecutor.isControlFlow` calls to accept
   *  `DSLNonLocalControlTransferException`: {{{
   *    TxnExecutor.transformDefault { e =>
   *      e.withControlFlowRecognizer {
   *        case _: DSLNonLocalControlTransferException => true
   *      }
   *    }
   *  }}}
   */
  def withControlFlowRecognizer(pf: PartialFunction[Throwable, Boolean]): TxnExecutor

  /** Returns a function that records, reports or discards exceptions that were
   *  thrown from a while-committing, after-commit or after-rollback life-cycle
   *  callback.
   */
  def postDecisionFailureHandler: (Txn.Status, Throwable) => Unit

  /** Returns a `TxnExecutor e` that is identical to this one, except that
   *  `e.postDecisionFailureHandler` will return `handler`.  This function may
   *  be called from inside a function passed to `TxnExecutor.transformDefault`
   *  to change the system-wide post-decision failure handler.
   */
  def withPostDecisionFailureHandler(handler: (Txn.Status, Throwable) => Unit): TxnExecutor
}
