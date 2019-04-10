/* scala-stm - (c) 2009-2012, Stanford University, PPL */

package scala.concurrent.stm
package ccstm

// TxnLocalImpl

private[ccstm] class TxnLocalImpl[A](init: => A,
                                     initialValue: InTxn => A,
                                     beforeCommit: InTxn => Unit,
                                     whilePreparing: InTxnEnd => Unit,
                                     whileCommitting: InTxnEnd => Unit,
                                     afterCommit: A => Unit,
                                     afterRollback: Txn.Status => Unit,
                                     afterCompletion: Txn.Status => Unit) extends Handle[A] with TxnLocal[A] {

  //////// stateless Handle

  def meta: Long = CCSTM.txnLocalMeta
  def meta_=(v: Long) = throw new Error
  def metaCAS(before: Long, after: Long): Boolean = throw new Error
  def base: AnyRef = this
  def offset: Int = 0
  def metaOffset: Int = 0
  def data: A = throw new Error
  def data_=(v: A) {}


  //////// TxnLocal

  def isInitialized(implicit txn: InTxnEnd): Boolean = {
    txn.asInstanceOf[InTxnImpl].txnLocalFind(this) >= 0
  }

  //////// SourceLike

  def get(implicit txn: InTxnEnd): A = {
    val impl = txn.asInstanceOf[InTxnImpl]
    val i = impl.txnLocalFind(this)
    if (i >= 0)
      impl.txnLocalGet[A](i)
    else
      initialize(impl)
  }

  private def initialize(impl: InTxnImpl): A = {
    if (initialValue != null || beforeCommit != null)
      impl.requireActive()

    val v = if (initialValue != null) initialValue(impl) else init
    impl.txnLocalInsert(this, v)

    registerCallbacks(impl)

    v
  }

  private def registerCallbacks(impl: InTxnImpl) {
    // need to do afterRollback and afterCompletion first so that if there is a
    // remote txn cancel we've got them in place
    if (afterRollback != null)
      impl.afterRollback(afterRollback)
    if (afterCompletion != null)
      impl.afterCompletion(afterCompletion)

    if (beforeCommit != null)
      impl.beforeCommit(beforeCommit)
    if (whilePreparing != null)
      impl.whilePreparing(whilePreparing)
    if (whileCommitting != null)
      impl.whileCommitting(whileCommitting)
    if (afterCommit != null) {
      impl.whileCommitting { _ =>
        val finalValue = impl.txnLocalGet[A](impl.txnLocalFind(this))
        impl.afterCommit { _ => afterCommit(finalValue) }
      }
    }
  }

  def getWith[Z](f: (A) => Z)(implicit txn: InTxnEnd): Z = f(get)

  def relaxedGet(equiv: (A, A) => Boolean)(implicit txn: InTxnEnd): A = get

  //////// SinkLike

  def set(v: A)(implicit txn: InTxnEnd) = {
    val impl = txn.asInstanceOf[InTxnImpl]
    val i = impl.txnLocalFind(this)
    if (i >= 0)
      impl.txnLocalUpdate(i, v)
    else {
      impl.txnLocalInsert(this, v)
      registerCallbacks(impl)
    }
  }

  def trySet(v: A)(implicit txn: InTxnEnd): Boolean = { set(v) ; true }

  //////// RefLike

  def swap(v: A)(implicit txn: InTxnEnd): A = { val z = get ; set(v) ; z }

  def transform(f: (A) => A)(implicit txn: InTxnEnd) { set(f(get)) }

  def transformIfDefined(pf: PartialFunction[A, A])(implicit txn: InTxnEnd): Boolean = {
    val v0 = get
    pf.isDefinedAt(v0) && { set(pf(v0)) ; true }
  }
}
