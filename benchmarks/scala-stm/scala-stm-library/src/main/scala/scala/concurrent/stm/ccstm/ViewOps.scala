/* scala-stm - (c) 2009-2012, Stanford University, PPL */

package scala.concurrent.stm
package ccstm

import java.util.concurrent.TimeUnit

/** The default implementation of `Ref.View`'s operations in CCSTM. */
private[ccstm] trait ViewOps[T] extends Ref.View[T] with Handle.Provider[T] {
  
  def handle: Handle[T]

  def get: T = InTxnImpl.dynCurrentOrNull match {
    case null => NonTxn.get(handle)
    case txn => txn.get(handle)
  }
  def getWith[Z](f: T => Z): Z = InTxnImpl.dynCurrentOrNull match {
    case null => f(NonTxn.get(handle))
    case txn => txn.getWith(handle, f)
  }
  def relaxedGet(equiv: (T, T) => Boolean): T = InTxnImpl.dynCurrentOrNull match {
    case null => NonTxn.get(handle)
    case txn => txn.relaxedGet(handle, equiv)
  }
  def await(f: T => Boolean): Unit = InTxnImpl.dynCurrentOrNull match {
    case null => NonTxn.await(handle, f)
    case txn => if (!f(txn.get(handle))) Txn.retry(txn)
  }
  def tryAwait(timeout: Long, unit: TimeUnit)(f: T => Boolean): Boolean = InTxnImpl.dynCurrentOrNull match {
    case null => NonTxn.tryAwait(handle, f, unit.toNanos(timeout))
    case txn => f(txn.get(handle)) || { Txn.retryFor(timeout, unit)(txn) ; false }
  }
  def set(v: T): Unit = InTxnImpl.dynCurrentOrNull match {
    case null => NonTxn.set(handle, v)
    case txn => txn.set(handle, v)
  }
  def trySet(v: T): Boolean = InTxnImpl.dynCurrentOrNull match {
    case null => NonTxn.trySet(handle, v)
    case txn => txn.trySet(handle, v)
  }
  def swap(v: T): T = InTxnImpl.dynCurrentOrNull match {
    case null => NonTxn.swap(handle, v)
    case txn => txn.swap(handle, v)
  }
  def compareAndSet(before: T, after: T): Boolean = InTxnImpl.dynCurrentOrNull match {
    case null => NonTxn.compareAndSet(handle, before, after)
    case txn => txn.compareAndSet(handle, before, after)
  }
  def compareAndSetIdentity[R <: AnyRef with T](before: R, after: T): Boolean = InTxnImpl.dynCurrentOrNull match {
    case null => NonTxn.compareAndSetIdentity(handle, before, after)
    case txn => txn.compareAndSetIdentity(handle, before, after)
  }
  def transform(f: T => T): Unit = InTxnImpl.dynCurrentOrNull match {
    case null => NonTxn.transformAndGet(handle, f)
    case txn => txn.transformAndGet(handle, f)
  }
  def getAndTransform(f: T => T): T = InTxnImpl.dynCurrentOrNull match {
    case null => NonTxn.getAndTransform(handle, f)
    case txn => txn.getAndTransform(handle, f)
  }
  def transformAndGet(f: T => T): T = InTxnImpl.dynCurrentOrNull match {
    case null => NonTxn.transformAndGet(handle, f)
    case txn => txn.transformAndGet(handle, f)
  }
  override def transformAndExtract[V](f: T => (T,V)): V = InTxnImpl.dynCurrentOrNull match {
    case null => NonTxn.transformAndExtract(handle, f)
    case txn => txn.transformAndExtract(handle, f)
  }

  def transformIfDefined(pf: PartialFunction[T,T]): Boolean = InTxnImpl.dynCurrentOrNull match {
    case null => NonTxn.transformIfDefined(handle, pf)
    case txn => txn.transformIfDefined(handle, pf)
  }
}
