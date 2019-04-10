/* scala-stm - (c) 2009-2012, Stanford University, PPL */

package scala.concurrent.stm
package ccstm

import scala.util.control.ControlThrowable

private[ccstm] object CCSTMExecutor {
  val DefaultControlFlowTest = { x: Throwable => x.isInstanceOf[ControlThrowable] }

  val DefaultPostDecisionFailureHandler = { (status: Txn.Status, x: Throwable) =>
    new Exception("status=" + status, x).printStackTrace()
  }
}

private[ccstm] case class CCSTMExecutor private (
       retryTimeoutNanos: Option[Long],
       controlFlowTest: Throwable => Boolean,
       postDecisionFailureHandler: (Txn.Status, Throwable) => Unit
    ) extends TxnExecutor {

  def this() = this(None, CCSTMExecutor.DefaultControlFlowTest, CCSTMExecutor.DefaultPostDecisionFailureHandler)

  def apply[Z](block: InTxn => Z)(implicit mt: MaybeTxn): Z = InTxnImpl().atomic(this, block)

  def oneOf[Z](blocks: (InTxn => Z)*)(implicit mt: MaybeTxn): Z = InTxnImpl().atomicOneOf(this, blocks)

  def unrecorded[Z](block: InTxn => Z, outerFailure: Txn.RollbackCause => Z)(implicit mt: MaybeTxn) = {
    InTxnImpl().unrecorded(this, block, outerFailure)
  }

  def pushAlternative[Z](mt: MaybeTxn, block: (InTxn) => Z): Boolean = InTxnImpl().pushAlternative(block)

  def compareAndSet[A, B](a: Ref[A], a0: A, a1: A, b: Ref[B], b0: B, b1: B): Boolean = {
    val ah = a.asInstanceOf[Handle.Provider[A]].handle
    val bh = b.asInstanceOf[Handle.Provider[B]].handle
    InTxnImpl.dynCurrentOrNull match {
      case null => NonTxn.transform2[A, B, Boolean](ah, bh, { (av, bv) => if (a0 == av && b0 == bv) (a1, b1, true) else (av, bv, false) })
      case txn => a0 == txn.get(ah) && b0 == txn.get(bh) && { txn.set(ah, a1) ; txn.set(bh, b1) ; true }
    }
  }

  def compareAndSetIdentity[A <: AnyRef, B <: AnyRef](a: Ref[A], a0: A, a1: A, b: Ref[B], b0: B, b1: B): Boolean = {
    val aRead = a0 eq a1
    val bRead = b0 eq b1
    if (aRead && bRead)
      cci(a, a0, b, b0)
    else if (aRead)
      ccasi(a, a0, b, b0, b1)
    else if (bRead)
      ccasi(b, b0, a, a0, a1)
    else
      dcasi(a, a0, a1, b, b0, b1)
  }

  private def cci[A <: AnyRef, B <: AnyRef](a: Ref[A], a0: A, b: Ref[B], b0: B): Boolean = {
    val ah = a.asInstanceOf[Handle.Provider[A]].handle
    val bh = b.asInstanceOf[Handle.Provider[B]].handle
    InTxnImpl.dynCurrentOrNull match {
      case null => NonTxn.cci(ah, a0, bh, b0)
      case txn => (a0 eq txn.get(ah)) && (b0 eq txn.get(bh))
    }
  }

  private def ccasi[A <: AnyRef, B <: AnyRef](a: Ref[A], a0: A, b: Ref[B], b0: B, b1: B): Boolean = {
    val ah = a.asInstanceOf[Handle.Provider[A]].handle
    val bh = b.asInstanceOf[Handle.Provider[B]].handle
    InTxnImpl.dynCurrentOrNull match {
      case null => NonTxn.ccasi(ah, a0, bh, b0, b1)
      case txn => (a0 eq txn.get(ah)) && (b0 eq txn.get(bh)) && { txn.set(bh, b1) ; true }
    }
  }

  private def dcasi[A <: AnyRef, B <: AnyRef](a: Ref[A], a0: A, a1: A, b: Ref[B], b0: B, b1: B): Boolean = {
    val ah = a.asInstanceOf[Handle.Provider[A]].handle
    val bh = b.asInstanceOf[Handle.Provider[B]].handle
    InTxnImpl.dynCurrentOrNull match {
      case null => NonTxn.transform2[A, B, Boolean](ah, bh, { (av, bv) => if ((a0 eq av) && (b0 eq bv)) (a1, b1, true) else (av, bv, false) })
      case txn => (a0 eq txn.get(ah)) && (b0 eq txn.get(bh)) && { txn.set(ah, a1) ; txn.set(bh, b1) ; true }
    }
  }

  def withRetryTimeoutNanos(timeout: Option[Long]): TxnExecutor = copy(retryTimeoutNanos = timeout)

  def isControlFlow(x: Throwable): Boolean = controlFlowTest(x)
  
  def withControlFlowRecognizer(pf: PartialFunction[Throwable, Boolean]): TxnExecutor = {
    copy(controlFlowTest = { x: Throwable => if (pf.isDefinedAt(x)) pf(x) else controlFlowTest(x) })
  }

  def withPostDecisionFailureHandler(handler: (Txn.Status, Throwable) => Unit): TxnExecutor = {
    copy(postDecisionFailureHandler = handler)
  }

  override def toString: String = {
    ("CCSTMExecutor@" + hashCode.toHexString +
      "(retryTimeoutNanos=" + retryTimeoutNanos +
      ", controlFlowTest=" +
      (if (controlFlowTest eq CCSTMExecutor.DefaultControlFlowTest) "default" else controlFlowTest) +
      ", postDecisionFailureHandler=" +
      (if (postDecisionFailureHandler eq CCSTMExecutor.DefaultPostDecisionFailureHandler) "default" else postDecisionFailureHandler) +
      ")")
  }
}
