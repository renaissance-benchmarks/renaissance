/* scala-stm - (c) 2009-2014, Stanford University, PPL */

package scala.concurrent.stm.skel

import scala.collection.generic.CanBuildFrom
import scala.collection.mutable.{WrappedArray, Builder, ArrayLike, IndexedSeq}
import java.util.concurrent.atomic._
import annotation.tailrec


/** `AtomicArray` implements a fixed-length indexed sequence where reads and
 *  writes have volatile semantics.  In addition, it adds an atomic swap
 *  operation (`swap`) and an atomic compare-and-swap (`compareAndSet`).
 *  The collection is backed by one of the Java atomic array classes, with the
 *  best match chosen at construction time using a manifest.
 *
 *  Instances of `AtomicArray[T]` are backed by `AtomicIntegerArray` if `T` is
 *  a primitive of at most 32 bits (smaller values are padded rather than
 *  packed).  `AtomicArray[Long]` and `AtomicArray[Double]` are backed by
 *  `AtomicLongArray`.  All other instances of `AtomicArray[T]` are backed by
 *  `AtomicReferenceArray` (except for `AtomicArray[Unit]`).  Floats and
 *  doubles are stored using their raw bit representation.
 *
 *  This class is used in the implementation of the reference STM
 *  implementation, but it is standalone and may be generally useful.
 *
 *  @author Nathan Bronson
 */
abstract class AtomicArray[T] extends IndexedSeq[T] with ArrayLike[T, AtomicArray[T]] {

  // We choose to store Boolean-s (and other small primitives) each in their
  // own Int.  This wastes space.  Another option would be to pack values into
  // the elements of the underlying AtomicIntegerArray.  This would save space,
  // but would require a compareAndSet loop to implement update, which adds
  // complexity and would require some sort of back-off scheme to avoid
  // live-lock.  A third option would be to use sun.misc.Unsafe directly, in
  // which case volatile reads and writes of byte-sized memory locations can be
  // performed directly.  compareAndSet of bytes would have to be emulated by
  // integer-sized CAS.

  override protected[this] def thisCollection: AtomicArray[T] = this
  override protected[this] def toCollection(repr: AtomicArray[T]): AtomicArray[T] = repr

  /** The length of the array */
  def length: Int

  /** The element at given index, with volatile read semantics */
  def apply(index: Int): T

  /** Update element at given index, with volatile write semantics */
  def update(index: Int, elem: T)

  /** Atomic swap of the element at index */
  def swap(index: Int, elem: T): T

  /** Returns true iff previous value was expected, elem installed */
  def compareAndSet(index: Int, expected: T, elem: T): Boolean

  /** Retries compareAndSet until success, using f, then returns the old value */
  @tailrec
  final def getAndTransform(index: Int)(f: T => T): T = {
    val before = apply(index)
    if (compareAndSet(index, before, f(before))) before else getAndTransform(index)(f)
  }

  override def stringPrefix = "AtomicArray"
  
  /** Clones this object, including the underlying Array. */
  override def clone: AtomicArray[T] = {
    val b = newBuilder
    b.sizeHint(length)
    b ++= this
    b.result()
  }

  override def newBuilder: AtomicArrayBuilder[T] = throw new AbstractMethodError
}

object AtomicArray {

  def apply[T](size: Int)(implicit m: ClassManifest[T]): AtomicArray[T] = {
    (m.newArray(0).asInstanceOf[AnyRef] match {
      case x: Array[Boolean] => new ofBoolean(size)
      case x: Array[Byte]    => new ofByte(size)
      case x: Array[Short]   => new ofShort(size)
      case x: Array[Char]    => new ofChar(size)
      case x: Array[Int]     => new ofInt(size)
      case x: Array[Float]   => new ofFloat(size)
      case x: Array[Long]    => new ofLong(size)
      case x: Array[Double]  => new ofDouble(size)
      case x: Array[Unit]    => new ofUnit(size)
      case x: Array[AnyRef]  => new ofRef[AnyRef](size)
    }).asInstanceOf[AtomicArray[T]]
  }

  def apply(elems: Array[Boolean]) = new ofBoolean(new AtomicIntegerArray(elems map {if(_) 1 else 0}))
  def apply(elems: Array[Byte])    = new ofByte(   new AtomicIntegerArray(elems map {_.toInt}))
  def apply(elems: Array[Short])   = new ofShort(  new AtomicIntegerArray(elems map {_.toInt}))
  def apply(elems: Array[Char])    = new ofChar(   new AtomicIntegerArray(elems map {_.toInt}))
  def apply(elems: Array[Int])     = new ofInt(    new AtomicIntegerArray(elems))
  def apply(elems: Array[Float])   = new ofFloat(  new AtomicIntegerArray(elems map {java.lang.Float.floatToRawIntBits(_)}))
  def apply(elems: Array[Long])    = new ofLong(   new AtomicLongArray(elems))
  def apply(elems: Array[Double])  = new ofDouble( new AtomicLongArray(elems map {java.lang.Double.doubleToRawLongBits(_)}))
  def apply(elems: Array[Unit])    = new ofUnit(   elems.length)
  def apply[T <: AnyRef](elems: Array[T]) =
    new ofRef((new AtomicReferenceArray(elems.asInstanceOf[Array[AnyRef]])).asInstanceOf[AtomicReferenceArray[T]])

  def apply[T](elems: TraversableOnce[T])(implicit m: ClassManifest[T]): AtomicArray[T] = {
    val array: AnyRef = (elems match {
      case w: WrappedArray[_] => w.array // we're going to copy out regardless, no need to duplicate right now
      case _ => elems.toArray
    })
    val result = (array match {
      case x: Array[Boolean] => apply(x)
      case x: Array[Byte]    => apply(x)
      case x: Array[Short]   => apply(x)
      case x: Array[Char]    => apply(x)
      case x: Array[Int]     => apply(x)
      case x: Array[Float]   => apply(x)
      case x: Array[Long]    => apply(x)
      case x: Array[Double]  => apply(x)
      case x: Array[Unit]    => apply(x)
      case x: Array[AnyRef]  => apply(x)
    })
    result.asInstanceOf[AtomicArray[T]]
  }

  
  implicit def canBuildFrom[T](implicit m: ClassManifest[T]): CanBuildFrom[AtomicArray[_], T, AtomicArray[T]] = {
    new CanBuildFrom[AtomicArray[_], T, AtomicArray[T]] {
      def apply(from: AtomicArray[_]): Builder[T, AtomicArray[T]] = {
        val b = AtomicArrayBuilder of m
        b.sizeHint(from.length)
        b
      }
      def apply(): Builder[T, AtomicArray[T]] = AtomicArrayBuilder of m
    }
  }


  final class ofBoolean(elems: AtomicIntegerArray) extends AtomicArray[Boolean] {
    def this(size: Int) = this(new AtomicIntegerArray(size))

    private def decode(v: Int) = v != 0
    private def encode(elem: Boolean) = if (elem) 1 else 0

    def length = elems.length
    def apply(index: Int) = decode(elems.get(index))
    def update(index: Int, elem: Boolean): Unit = elems.set(index, encode(elem))
    def swap(index: Int, elem: Boolean) = decode(elems.getAndSet(index, encode(elem)))
    def compareAndSet(index: Int, expected: Boolean, elem: Boolean) =
      elems.compareAndSet(index, encode(expected), encode(elem))
    override def newBuilder = new AtomicArrayBuilder.ofBoolean
  }

  final class ofByte(elems: AtomicIntegerArray) extends AtomicArray[Byte] {
    def this(size: Int) = this(new AtomicIntegerArray(size))

    def length = elems.length
    def apply(index: Int) = elems.get(index).toByte
    def update(index: Int, elem: Byte): Unit = elems.set(index, elem)
    def swap(index: Int, elem: Byte) = elems.getAndSet(index, elem).toByte
    def compareAndSet(index: Int, expected: Byte, elem: Byte) =
      elems.compareAndSet(index, expected, elem)
    override def newBuilder = new AtomicArrayBuilder.ofByte
  }

  final class ofShort(elems: AtomicIntegerArray) extends AtomicArray[Short] {
    def this(size: Int) = this(new AtomicIntegerArray(size))

    def length = elems.length
    def apply(index: Int) = elems.get(index).toShort
    def update(index: Int, elem: Short): Unit = elems.set(index, elem)
    def swap(index: Int, elem: Short) = elems.getAndSet(index, elem).toShort
    def compareAndSet(index: Int, expected: Short, elem: Short) =
      elems.compareAndSet(index, expected, elem)
    override def newBuilder = new AtomicArrayBuilder.ofShort
  }

  final class ofChar(elems: AtomicIntegerArray) extends AtomicArray[Char] {
    def this(size: Int) = this(new AtomicIntegerArray(size))

    def length = elems.length
    def apply(index: Int) = elems.get(index).toChar
    def update(index: Int, elem: Char): Unit = elems.set(index, elem)
    def swap(index: Int, elem: Char) = elems.getAndSet(index, elem).toChar
    def compareAndSet(index: Int, expected: Char, elem: Char) =
      elems.compareAndSet(index, expected, elem)
    override def newBuilder = new AtomicArrayBuilder.ofChar
  }

  final class ofInt(elems: AtomicIntegerArray) extends AtomicArray[Int] {
    def this(size: Int) = this(new AtomicIntegerArray(size))

    def length = elems.length
    def apply(index: Int) = elems.get(index)
    def update(index: Int, elem: Int): Unit = elems.set(index, elem)
    def swap(index: Int, elem: Int) = elems.getAndSet(index, elem)
    def compareAndSet(index: Int, expected: Int, elem: Int) =
      elems.compareAndSet(index, expected, elem)
    override def newBuilder = new AtomicArrayBuilder.ofInt
  }

  final class ofFloat(elems: AtomicIntegerArray) extends AtomicArray[Float] {
    def this(size: Int) = this(new AtomicIntegerArray(size))

    private def decode(v: Int) = java.lang.Float.intBitsToFloat(v)
    private def encode(elem: Float) = java.lang.Float.floatToRawIntBits(elem)

    def length = elems.length
    def apply(index: Int) = decode(elems.get(index))
    def update(index: Int, elem: Float): Unit = elems.set(index, encode(elem))
    def swap(index: Int, elem: Float) = decode(elems.getAndSet(index, encode(elem)))
    def compareAndSet(index: Int, expected: Float, elem: Float) =
      elems.compareAndSet(index, encode(expected), encode(elem))
    override def newBuilder = new AtomicArrayBuilder.ofFloat
  }

  final class ofLong(elems: AtomicLongArray) extends AtomicArray[Long] {
    def this(size: Int) = this(new AtomicLongArray(size))

    def length = elems.length
    def apply(index: Int) = elems.get(index)
    def update(index: Int, elem: Long): Unit = elems.set(index, elem)
    def swap(index: Int, elem: Long) = elems.getAndSet(index, elem)
    def compareAndSet(index: Int, expected: Long, elem: Long) =
      elems.compareAndSet(index, expected, elem)
    override def newBuilder = new AtomicArrayBuilder.ofLong
  }

  final class ofDouble(elems: AtomicLongArray) extends AtomicArray[Double] {
    def this(size: Int) = this(new AtomicLongArray(size))

    private def decode(v: Long) = java.lang.Double.longBitsToDouble(v)
    private def encode(elem: Double) = java.lang.Double.doubleToRawLongBits(elem)

    def length = elems.length
    def apply(index: Int) = decode(elems.get(index))
    def update(index: Int, elem: Double): Unit = elems.set(index, encode(elem))
    def swap(index: Int, elem: Double) = decode(elems.getAndSet(index, encode(elem)))
    def compareAndSet(index: Int, expected: Double, elem: Double) =
      elems.compareAndSet(index, encode(expected), encode(elem))
    override def newBuilder = new AtomicArrayBuilder.ofDouble
  }
  
  final class ofUnit(val length: Int) extends AtomicArray[Unit] {
    private val dummy = new AtomicReference[Unit](())

    private def ref(index: Int): AtomicReference[Unit] = {
      if (index < 0 || index >= length)
        throw new IndexOutOfBoundsException
      dummy
    }
    
    def apply(index: Int) = ref(index).get
    def update(index: Int, elem: Unit): Unit = ref(index).set(elem)
    def swap(index: Int, elem: Unit) = ref(index).getAndSet(elem)
    def compareAndSet(index: Int, expected: Unit, elem: Unit) = ref(index).compareAndSet(expected, elem)
    override def newBuilder = new AtomicArrayBuilder.ofUnit
  }

  final class ofRef[T <: AnyRef](elems: AtomicReferenceArray[T]) extends AtomicArray[T] {
    def this(size: Int) = this(new AtomicReferenceArray[T](size))

    def length = elems.length
    def apply(index: Int) = elems.get(index)
    def update(index: Int, elem: T): Unit = elems.set(index, elem)
    def swap(index: Int, elem: T) = elems.getAndSet(index, elem)
    def compareAndSet(index: Int, expected: T, elem: T) = elems.compareAndSet(index, expected, elem)
    override def newBuilder = new AtomicArrayBuilder.ofRef[T]
  }
}
