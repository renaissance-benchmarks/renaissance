/* scala-stm - (c) 2009-2016, Stanford University, PPL */

package scala.concurrent.stm

import java.util.concurrent.TimeUnit

object CommitBarrier {

  /** A class that describes the reason that a commit barrier member was not
   *  committed.  Cancelled members might have been rolled back or might
   *  have been prevented from ever starting.
   */
  sealed abstract class CancelCause

  /** The `CancelCause` used when the `addMember` call that created a member
   *  was from inside a transaction that later rolled back.  This cancel
   *  cause does not necessarily imply that other members of the commit
   *  barrier didn't (or won't) eventually succeed.
   */
  case object CreatingTxnRolledBack extends CancelCause

  /** The `CancelCause` used when some members of the commit barrier did not
   *  finish in time.  Members may finish either by completing or by being
   *  cancelled.  This cancel cause implies that all members were eventually
   *  cancelled.
   */
  case object Timeout extends CancelCause

  /** The `CancelCause` used when some members of the commit barrier
   *  conflict with each other.  Since the commit barrier can only succeed
   *  if all of them commit simultaneously this would lead to a deadlock, so
   *  the entire commit barrier is instead cancelled.  This cancel cause
   *  implies that all members were eventually cancelled.
   * 
   *  `debugInfo` is optional information provided by the STM implementation
   *  to help locate the source of the avoided deadlock.  If provided it
   *  might be one of the `Ref`s in the cycle, or it might be a `String`
   *  describing the cycle.
   */
  case class MemberCycle(debugInfo: Any) extends CancelCause

  /** The `CancelCause` used when a member of the commit barrier cannot commit
   *  due to an uncaught exception (see `Txn.UncaughtExceptionCause`).  This
   *  cancel cause implies that all members of the commit barrier rolled back.
   *  The exception will be rethrown to the thread running the member that
   *  originally generated the exception, all other members will get this
   *  `CancelCause`.
   *
   *  This cancel cause will also be used if a member thread receives an
   *  interrupt while it is waiting for the commit barrier.
   */
  case class MemberUncaughtExceptionCause(x: Throwable) extends CancelCause

  /** A `CancelCause` provided for users of commit barriers, not used by the
   *  STM itself.  This cancel cause does not imply that other members of the
   *  commit barrier didn't (or won't) eventually succeed.
   */
  case class UserCancel(info: Any) extends CancelCause

  /** A participant in a synchronized group commit.  Each member of a commit
   *  barrier must arrange for either `atomic` or `cancel` to be called,
   *  otherwise the other members won't be able to commit.
   */
  trait Member {

    /** Returns the commit barrier of which this instance is a member. */
    def commitBarrier: CommitBarrier

    /** Returns the `TxnExecutor` that will be used by `atomic`.  This is
     *  initialized during construction to the default `TxnExecutor`
     *  (returned by `scala.concurrent.stm.atomic`).
     */
    def executor: TxnExecutor

    /** Changes the `TxnExecutor` that will be used by `atomic`. */
    def executor_=(v: TxnExecutor)

    /** Atomically executes `body` as part of a commit barrier, ensuring
     *  that if the transaction commits, all actions performed by all
     *  members of the commit barrier appear to occur simultaneously.  If
     *  the transaction commits then the value `v` returned by `body` is
     *  returned as `Right(v)`.  If this member is cancelled then this method
     *  returns `Left(c)`, where `c` describes the first cause passed to
     *  the `cancel` method.  If this member is not cancelled but the
     *  transaction is rolled back without the possibility of retry, then
     *  this method throws an exception the same as any other atomic block
     *  (see `TxnExecutor.apply`).
     * 
     *  It is not allowed to chain `orAtomic` onto this form of `atomic`,
     *  but you can accomplish the same effect with a nested atomic block:{{{
     *    member.atomic { implicit txn =>
     *      atomic { implicit txn =>
     *        ... first alternative
     *      } orAtomic { implicit txn =>
     *        ... second alternative
     *      }
     *    }
     *  }}}
     * 
     *  In the current version of ScalaSTM this method may only be used if
     *  there is no enclosing transaction; an STM implementation may throw
     *  `IllegalStateException` if there is already an active transaction on
     *  this thread.  This restriction might be relaxed in the future if
     *  there is a use case for it (and a semantics for how it should work).
     * 
     *  @param underlying the `TxnExecutor` that should be used to actually
     *         execute the transaction, defaulting to the STM's default
     *  @param body the code to run atomically
     *  @return `Right(v)` where `v` is the result of successfully running
     *          `body` in an atomic block, or `Left(c)` where `c` is the
     *          reason for this member's cancellation
     *  @throws IllegalStateException if called from inside the dynamic
     *          scope of an existing transaction and that is not supported
     *          by the chosen STM implementation
     */
    def atomic[Z](body: InTxn => Z): Either[CancelCause, Z]

    /** Removes this member from the commit barrier, and causes any pending
     *  or future calls to `this.atomic` to return a `Left`.  If the commit
     *  barrier has already committed successfully this method throws
     *  `IllegalStateException`.  It is safe to call this method multiple
     *  times.
     * 
     *  @param cause the cancel cause to return from `atomic`
     *  @throws IllegalStateException if the commit barrier has already
     *          decided to commit
     */
    def cancel(cause: UserCancel)
  }

  /** Constructs and returns a new `CommitBarrier` in which each member will
   *  wait at most `timeout` `unit` for other members of the barrier to
   *  become ready to commit.  If timeout occurs all members will be
   *  cancelled with a `CancelCause` of `Timeout`.  Each commit barrier may
   *  be used for at most one coordinated commit (it is not cyclic).
   */
  @deprecated("The current CommitBarrier implementation doesn't have proper deadlock avoidance, please avoid if possible", "0.8")
  def apply(timeout: Long, unit: TimeUnit = TimeUnit.MILLISECONDS): CommitBarrier =
      impl.STMImpl.instance.newCommitBarrier(timeout, unit)
}

/** A `CommitBarrier` allows multiple transactions on separate threads to
 *  perform a single atomic commit.  All of the actions performed by all of
 *  the atomic blocks executed by members of the barrier will appear to
 *  occur as a single atomic action, even though they are spread across
 *  multiple threads.
 * 
 *  Commit barriers can be used to implement transactors, where actions
 *  taken by multiple actors should be atomic as a single unit.
 * 
 *  Because there is no ordering possible between the atomic blocks that
 *  make up a commit barrier, if those transactions conflict then the only
 *  way to avoid deadlock is to roll back all of the barrier's members.  If
 *  you observe a cancel cause of `CommitBarrier.MemberCycle` then this has
 *  happened to you, and you need to run more of the logic on a single
 *  thread inside a single transaction.
 * 
 *  This abstraction is based on Multiverse's `CountDownCommitBarrier`, by
 *  Peter Veentjer.
 * 
 *  @author Nathan Bronson
 */
trait CommitBarrier {
  import CommitBarrier._

  /** Adds a new member to this coordinated commit and returns a `Member`
   *  instance that should be used to execute this member's atomic block.
   *  If the existing members of this commit barrier have already completed
   *  (committed or rolled back) then it is not possible to join the commit
   *  and this method will throw `IllegalStateException`.
   * 
   *  If a member is added from inside a transaction and that transaction is
   *  later rolled back, the member will be removed from the commit barrier
   *  (by `Member.cancel(CreatingTxnRolledBack)`), unless
   *  `cancelOnLocalRollback` is false.
   * 
   *  @param cancelOnLocalRollback controls whether the newly created member
   *         will be automatically cancelled if this call to `addMember` is
   *         from inside a transaction that later rolls back
   *  @throws IllegalStateException if this commit barrier has already been
   *          completed (committed or rolled back)
   */
  def addMember(cancelOnLocalRollback: Boolean = true)(implicit txn: MaybeTxn): Member
}
