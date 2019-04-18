/* scala-stm - (c) 2009-2012, Stanford University, PPL */

package scala.concurrent.stm
package ccstm

/** The default implementation of `Ref`'s operations in CCSTM. */
private[ccstm] trait RefOps[T] extends Ref[T] with Handle.Provider[T] {

  private def impl(implicit txn: InTxn): InTxnImpl = txn.asInstanceOf[InTxnImpl]

  /** Override this to provide the handle that this `RefOps` uses. */
  def handle: Handle[T]

  //////////////// Source stuff

  override def apply()(implicit txn: InTxn): T = impl.get(handle)
  def get(implicit txn: InTxn): T = impl.get(handle)
  def getWith[Z](f: (T) => Z)(implicit txn: InTxn): Z = impl.getWith(handle, f)
  def relaxedGet(equiv: (T, T) => Boolean)(implicit txn: InTxn): T = impl.relaxedGet(handle, equiv)

  //////////////// Sink stuff


  override def update(v: T)(implicit txn: InTxn) { impl.set(handle, v) }
  def set(v: T)(implicit txn: InTxn) { impl.set(handle, v) }
  def trySet(v: T)(implicit txn: InTxn): Boolean = impl.trySet(handle, v)

  //////////////// Ref stuff

  def swap(v: T)(implicit txn: InTxn): T = impl.swap(handle, v)

  def transform(f: T => T)(implicit txn: InTxn) {
    // only sub-types of Ref actually perform deferral, the base implementation
    // evaluates f immediately
    impl.getAndTransform(handle, f)
  }

  override def transformAndGet(f: T => T)(implicit txn: InTxn): T = impl.transformAndGet(handle, f)

  override def getAndTransform(f: T => T)(implicit txn: InTxn): T = impl.getAndTransform(handle, f)

  override def transformAndExtract[V](f: T => (T,V))(implicit txn: InTxn): V = impl.transformAndExtract(handle, f)

  def transformIfDefined(pf: PartialFunction[T,T])(implicit txn: InTxn): Boolean = {
    impl.transformIfDefined(handle, pf)
  }
}
