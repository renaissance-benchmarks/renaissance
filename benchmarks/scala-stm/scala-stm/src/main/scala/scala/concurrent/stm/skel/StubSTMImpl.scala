/* scala-stm - (c) 2009-2012, Stanford University, PPL */

package scala.concurrent.stm
package skel

import java.lang.Throwable
import scala.collection.mutable.Builder
import java.util.concurrent.TimeUnit

class StubSTMImpl extends impl.STMImpl {

  //////// RefFactory

  def newRef(v0: Boolean): Ref[Boolean] = throw new AbstractMethodError
  def newRef(v0: Byte): Ref[Byte] = throw new AbstractMethodError
  def newRef(v0: Short): Ref[Short] = throw new AbstractMethodError
  def newRef(v0: Char): Ref[Char] = throw new AbstractMethodError
  def newRef(v0: Int): Ref[Int] = throw new AbstractMethodError
  def newRef(v0: Float): Ref[Float] = throw new AbstractMethodError
  def newRef(v0: Long): Ref[Long] = throw new AbstractMethodError
  def newRef(v0: Double): Ref[Double] = throw new AbstractMethodError
  def newRef(v0: Unit): Ref[Unit] = throw new AbstractMethodError
  def newRef[A : ClassManifest](v0: A): Ref[A] = throw new AbstractMethodError

  def newTxnLocal[A](init: => A,
                     initialValue: InTxn => A,
                     beforeCommit: InTxn => Unit,
                     whilePreparing: InTxnEnd => Unit,
                     whileCommitting: InTxnEnd => Unit,
                     afterCommit: A => Unit,
                     afterRollback: Txn.Status => Unit,
                     afterCompletion: Txn.Status => Unit): TxnLocal[A] = throw new AbstractMethodError

  def newTArray[A : ClassManifest](length: Int): TArray[A] = throw new AbstractMethodError
  def newTArray[A : ClassManifest](xs: TraversableOnce[A]): TArray[A] = throw new AbstractMethodError

  def newTMap[A, B]: TMap[A, B] = throw new AbstractMethodError
  def newTMapBuilder[A, B]: Builder[(A, B), TMap[A, B]] = throw new AbstractMethodError

  def newTSet[A]: TSet[A] = throw new AbstractMethodError
  def newTSetBuilder[A]: Builder[A, TSet[A]] = throw new AbstractMethodError

  //////// TxnContext

  def findCurrent(implicit mt: MaybeTxn): Option[InTxn] = throw new AbstractMethodError
  def dynCurrentOrNull: InTxn = throw new AbstractMethodError

  //////// TxnExecutor

  def apply[Z](block: InTxn => Z)(implicit mt: MaybeTxn): Z = throw new AbstractMethodError
  def oneOf[Z](blocks: (InTxn => Z)*)(implicit mt: MaybeTxn): Z = throw new AbstractMethodError
  def unrecorded[Z](block: InTxn => Z, outerFailure: Txn.RollbackCause => Z)(implicit mt: MaybeTxn): Z = throw new AbstractMethodError
  def pushAlternative[Z](mt: MaybeTxn, block: InTxn => Z): Boolean = throw new AbstractMethodError
  def compareAndSet[A, B](a: Ref[A], a0: A, a1: A, b: Ref[B], b0: B, b1: B): Boolean = throw new AbstractMethodError
  def compareAndSetIdentity[A <: AnyRef, B <: AnyRef](a: Ref[A], a0: A, a1: A, b: Ref[B], b0: B, b1: B): Boolean = throw new AbstractMethodError
  def retryTimeoutNanos: Option[Long] = throw new AbstractMethodError
  def withRetryTimeoutNanos(timeout: Option[Long]): TxnExecutor = throw new AbstractMethodError
  def isControlFlow(x: Throwable): Boolean = throw new AbstractMethodError
  def withControlFlowRecognizer(pf: PartialFunction[Throwable, Boolean]): TxnExecutor = throw new AbstractMethodError
  def postDecisionFailureHandler: (Txn.Status, Throwable) => Unit = throw new AbstractMethodError
  def withPostDecisionFailureHandler(handler: (Txn.Status, Throwable) => Unit): TxnExecutor = throw new AbstractMethodError

  //////// STMImpl

  def newCommitBarrier(timeout: Long, unit: TimeUnit): CommitBarrier = throw new AbstractMethodError
}
