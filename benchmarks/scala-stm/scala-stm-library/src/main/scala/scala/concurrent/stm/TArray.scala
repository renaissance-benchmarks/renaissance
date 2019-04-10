/* scala-stm - (c) 2009-2012, Stanford University, PPL */

package scala.concurrent.stm

import scala.collection.{mutable, immutable}

object TArray {

  /** A view that supports accesses to a `TArray` instance outside the static
   *  scope of a `Txn`.  `TArray.View` is to `TArray` as `Ref.View` is to
   *  `Ref`.
   */
  trait View[A] extends mutable.IndexedSeq[A] with TxnDebuggable {
    /** The `TArray` from which this view was created. */
    def tarray: TArray[A]

    def length: Int

    /** Performs an atomic read of the `index`th element of `array`.  If an
     *  atomic block is active (see `Txn.findCurrent`) then the read will be
     *  performed as part of the transaction, otherwise it will act as if it
     *  was performed inside a new atomic block.
     */
    def apply(index: Int): A

    /** Performs an atomic write of the `index`th element of `array`.  If an
     *  atomic block is active (see `Txn.findCurrent`) then the write will be
     *  performed as part of the transaction, otherwise it will act as if it
     *  was performed inside a new atomic block.
     */
    def update(index: Int, v: A)

    /** Returns a sequence of `Ref.View` that are backed by the elements of
     *  `array`.  All operations on the contained `Ref.View`s are supported.
     */
    def refViews: immutable.IndexedSeq[Ref.View[A]]
  }

  //////////////// factory methods

  // We don't include apply(xs: A*) because it is surprising when
  // TArray[Int](1000) creates a TArray of length 1.

  /** Returns a new `TArray[A]` containing `length` copies of the default value
   *  for elements of type `A`.
   */
  def ofDim[A : ClassManifest](length: Int): TArray[A] = impl.STMImpl.instance.newTArray[A](length)

  /** Returns a new `TArray[A]` containing the elements of `data`. */
  def apply[A : ClassManifest](data: TraversableOnce[A]): TArray[A] = impl.STMImpl.instance.newTArray[A](data)
}

/** Bulk transactional storage, roughly equivalent to `Array[Ref[T]]` but
 *  potentially much more space efficient.  Elements can be read and written
 *  directly, or the `refs` method can be used to obtain transient `Ref`
 *  instances backed by the elements of the `TArray`.
 *
 *  @author Nathan Bronson
 */
trait TArray[A] extends TxnDebuggable {

  /** Returns the length of this `TArray`, which does not change. */
  def length: Int

  /** Performs a transactional read of the `index`th element of this
   *  transactional array.  Equivalent to `refs(index).get`.
   */
  def apply(index: Int)(implicit txn: InTxn): A

  /** Performs a transactional write to the `index`th element of this
   *  transactional array.  Equivalent to `refs(index).set(v)`.
   */
  def update(index: Int, v: A)(implicit txn: InTxn)

  /** Returns a `TArray.View` that allows access to the contents of this
   *  `TArray` without requiring that an `InTxn` be available.  See `Ref.View`.
   */
  def single: TArray.View[A]

  /** Returns a sequence of `Ref` instances that are backed by elements of this
   *  `TArray`.  All operations on the contained `Ref`s are supported.
   *
   *  As an example, the following code tests whether `a(i)` is greater than
   *  10 without requiring the transaction to roll back for all writes to
   *  `a(i)`: {{{
   *    atomic { implicit t =>
   *      if (a.refs(i).getWith( _ > 10 )) {
   *        ... lots of stuff
   *      }
   *    }
   *  }}}
   */
  def refs: immutable.IndexedSeq[Ref[A]]
}
