/* scala-stm - (c) 2009-2012, Stanford University, PPL */

package scala.concurrent.stm
package ccstm

import skel.AtomicArray
import java.util.concurrent.atomic.AtomicLongArray
import scala.reflect.ClassManifest
import scala.collection._


private[ccstm] class TArrayImpl[A](private val values: AtomicArray[A])(implicit m: ClassManifest[A]) extends TArray[A] with TArray.View[A] {
  import TArray._

  def this(length0: Int)(implicit m: ClassManifest[A]) = this(AtomicArray[A](length0))

  def this(data0: TraversableOnce[A])(implicit m: ClassManifest[A]) = this(AtomicArray[A](data0))

  val length = values.length

  //////////////// TArray

  def single: View[A] = this

  def apply(index: Int)(implicit txn: InTxn) = getRef(index).get

  def update(index: Int, v: A)(implicit txn: InTxn) = getRef(index).set(v)

  /** Returns a sequence that will produce transient `Ref` instances that are
   *  backed by elements of this `TArray`.  This allows use of all of `Ref`'s
   *  functionality for reading, writing, and transforming elements.
   */
  def refs: immutable.IndexedSeq[Ref[A]] = new immutable.IndexedSeq[Ref[A]] {
    def length: Int = TArrayImpl.this.length
    def apply(index0: Int): Ref[A] = getRef(index0)
  }

  //////////////// TArray.View

  def tarray = TArrayImpl.this

  def apply(index: Int): A = getRef(index).single.get

  def update(index: Int, v: A) = getRef(index).single.set(v)

  def refViews: immutable.IndexedSeq[Ref.View[A]] = new immutable.IndexedSeq[Ref.View[A]] {
    def length = tarray.length
    def apply(index: Int) = getRef(index).single
  }

  /////////////// TxnDebuggable

  def dbgStr: String = atomic.unrecorded({ _ => mkStringPrefix("TArray", single) }, { _.toString })

  def dbgValue: Any = atomic.unrecorded({ _ => toArray }, { x => x })

  /////////////// Internal implementation

  private val metaIndexMask = {
    // We use min(length, nextPowerOfTwo(6 + length/16)) metadata elements.
    // The mask is always nextPowerOfTwo(6 + length/16) - 1, even if that is
    // too large.
    val n = 6 + length / 16
    var m = 7
    while (m < n - 1)
      m = (m << 1) + 1
    m
  }

  private val metaValues = new AtomicLongArray(math.min(metaIndexMask + 1, length))

  private def getRef(index: Int): Ref[A] = {
    if (index < 0 || index >= length)
      throw new ArrayIndexOutOfBoundsException(index)

    new Handle[A] with RefOps[A] with ViewOps[A] {
      def handle: Handle[A] = this
      def single: Ref.View[A] = this
      def ref: Ref[A] = this

      def meta = metaValues.get(metaOffset)
      def meta_=(v: Long) { metaValues.set(metaOffset, v) }
      def metaCAS(before: Long, after: Long) = metaValues.compareAndSet(metaOffset, before, after)
      def base = TArrayImpl.this
      def offset = index
      def metaOffset = index & metaIndexMask
      def data = values(index)
      def data_=(v: A) { values(index) = v }

      override def dbgStr: String = super[RefOps].dbgStr
      override def dbgValue: Any = super[RefOps].dbgValue

      override def toString = {
        "TArray@" + Integer.toHexString(System.identityHashCode(TArrayImpl.this)) + "(" + index + ")"
      }
    }
  }
}

