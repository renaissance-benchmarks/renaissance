/* scala-stm - (c) 2009-2011, Stanford University, PPL */

package scala.concurrent.stm

/** The presence of an implicit `InTxnEnd` instance inside a transaction
 *  life-cycle handler grants permission to call methods in `object Txn` that
 *  locate nesting levels or register additional handlers.  This functionality
 *  is separated from that granted by `InTxn` because `Ref` operations are not
 *  allowed from handlers after commit has begun.
 *
 *  @author Nathan Bronson
 */
trait InTxnEnd extends MaybeTxn {
  import Txn._

  // The user-visible versions of these methods are in the Txn object.

  protected[stm] def status: Status
  protected[stm] def rootLevel: NestingLevel
  protected[stm] def currentLevel: NestingLevel
  protected[stm] def rollback(cause: RollbackCause): Nothing
  protected[stm] def retry(): Nothing
  protected[stm] def retryFor(timeoutNanos: Long)
  protected[stm] def beforeCommit(handler: InTxn => Unit)
  protected[stm] def whilePreparing(handler: InTxnEnd => Unit)
  protected[stm] def whileCommitting(handler: InTxnEnd => Unit)
  protected[stm] def afterCommit(handler: Status => Unit)
  protected[stm] def afterRollback(handler: Status => Unit)
  protected[stm] def afterCompletion(handler: Status => Unit)
  protected[stm] def setExternalDecider(decider: ExternalDecider)
}
