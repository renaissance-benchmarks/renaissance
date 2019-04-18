/* scala-stm - (c) 2009-2011, Stanford University, PPL */

package scala.concurrent.stm

object NestingLevel {

  /** Returns the `NestingLevel` that represents the current atomic block
   *  execution attempt.
   */
  def current(implicit txn: InTxnEnd): NestingLevel = txn.currentLevel

  /** Returns the `NestingLevel` that represents the outermost atomic block
   *  that is currently being attempted.
   */
  def root(implicit txn: InTxnEnd): NestingLevel = txn.rootLevel
}

/** A `NestingLevel` instance describes a single attempt to execute an atomic
 *  block inside a transaction.  Reads and writes performed by a transaction
 *  will only be made visible to other threads after (if) the root nesting
 *  level commits.
 *
 *  Methods on this class may be called from any thread, and may be called
 *  after the corresponding execution attempt has been completed.
 *
 *  @author Nathan Bronson
 */
trait NestingLevel {
  import Txn._

  /** Returns the `TxnExecutor` in which this attempt is executing. */
  def executor: TxnExecutor

  /** Returns the nearest enclosing nesting level, if any. */
  def parent: Option[NestingLevel]

  /** Returns the outermost enclosing nested transaction context, or this
   *  instance if it is the outermost nesting level.  It is always true that
   *  `a.parent.isEmpty == (a.root == a)`.
   */
  def root: NestingLevel

  /** Returns a snapshot of this nesting level's current status.  The status
   *  may change to `Txn.RolledBack` due to the actions of a concurrent
   *  thread.  This method may be called from any thread.
   */
  def status: Status

  /** Requests that a transaction attempt be marked for rollback, possibly
   *  also rolling back some or all of the enclosing nesting levels.  Returns
   *  the resulting status, which will be one of `Prepared`, `Committed` or
   *  `RolledBack`.  Regardless of the status, this method does not throw an
   *  exception.
   *
   *  Unlike `Txn.rollback(cause)`, this method may be called from any thread.
   *  Note that there is no facility for remotely triggering a rollback during
   *  the `Prepared` state, as the `ExplicitDecider` is given the final choice.
   */
  def requestRollback(cause: RollbackCause): Status
}
