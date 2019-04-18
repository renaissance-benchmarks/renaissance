/* scala-stm - (c) 2009-2012, Stanford University, PPL */

package scala.concurrent

import java.util.concurrent.TimeUnit

package object stm {

  /** Atomically executes atomic blocks using the default `TxnExecutor`.  See
   *  `TxnExecutor.apply`.
   */
  def atomic: scala.concurrent.stm.TxnExecutor = scala.concurrent.stm.TxnExecutor.defaultAtomic

  /** Equivalent to `Txn.retry`. */
  def retry(implicit txn: scala.concurrent.stm.InTxn): Nothing = scala.concurrent.stm.Txn.retry

  /** Equivalent to `Txn.retryFor(timeout, unit)`. */
  def retryFor(timeout: Long, unit: TimeUnit = TimeUnit.MILLISECONDS)(implicit txn: scala.concurrent.stm.InTxn) {
    scala.concurrent.stm.Txn.retryFor(timeout, unit)
  }

  /** This is the first half of the machinery for implementing `orAtomic`. */
  implicit def wrapChainedAtomic[A](lhs: => A) = new scala.concurrent.stm.PendingAtomicBlock(lhs)
}
