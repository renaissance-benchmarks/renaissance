/* scala-stm - (c) 2009-2010, Stanford University, PPL */

package scala.concurrent.stm
package skel

private[stm] trait AbstractNestingLevel extends NestingLevel {
  import Txn._

  def txn: AbstractInTxn
  def parLevel: AbstractNestingLevel
  override def root: AbstractNestingLevel

  def parent: Option[NestingLevel] = Option(parLevel)

  private[skel] var _beforeCommitSize = 0
  private[skel] var _whileValidatingSize = 0
  private[skel] var _whilePreparingSize = 0
  private[skel] var _whileCommittingSize = 0
  private[skel] var _afterCommitSize = 0
  private[skel] var _afterRollbackSize = 0
}
