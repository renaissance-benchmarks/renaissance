/* scala-stm - (c) 2009-2011, Stanford University, PPL */

package scala.concurrent.stm
package skel

class StubInTxn extends InTxn {
  import concurrent.stm.Txn._

  def executor: TxnExecutor = throw new AbstractMethodError
  def status: Status = throw new AbstractMethodError
  def rootLevel: NestingLevel = throw new AbstractMethodError
  def currentLevel: NestingLevel = throw new AbstractMethodError
  def rollback(cause: RollbackCause): Nothing = throw new AbstractMethodError
  def retry(): Nothing = throw new AbstractMethodError
  def retryFor(timeoutNanos: Long) { throw new AbstractMethodError }
  def beforeCommit(handler: InTxn => Unit) = throw new AbstractMethodError
  def whilePreparing(handler: InTxnEnd => Unit) = throw new AbstractMethodError
  def whileCommitting(handler: InTxnEnd => Unit) = throw new AbstractMethodError
  def afterCommit(handler: Status => Unit) = throw new AbstractMethodError
  def afterRollback(handler: Status => Unit) = throw new AbstractMethodError
  def afterCompletion(handler: Status => Unit) = throw new AbstractMethodError
  def setExternalDecider(decider: ExternalDecider) = throw new AbstractMethodError
}
