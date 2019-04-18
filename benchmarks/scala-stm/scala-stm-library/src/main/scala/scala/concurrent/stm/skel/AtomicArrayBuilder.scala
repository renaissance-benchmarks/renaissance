/* scala-stm - (c) 2009-2011, Stanford University, PPL */

package scala.concurrent.stm.skel

import scala.collection.mutable.Builder
import java.util.concurrent.atomic.{AtomicReferenceArray, AtomicLongArray, AtomicIntegerArray}

trait AtomicArrayBuilder[A] extends Builder[A, AtomicArray[A]]

object AtomicArrayBuilder {
  def of[T](m: ClassManifest[T]): Builder[T, AtomicArray[T]] = {
    (m.newArray(0).asInstanceOf[AnyRef] match {
      case x: Array[Boolean] => new ofBoolean
      case x: Array[Byte] => new ofByte
      case x: Array[Short] => new ofShort
      case x: Array[Char] => new ofChar
      case x: Array[Int] => new ofInt
      case x: Array[Float] => new ofFloat
      case x: Array[Long] => new ofLong
      case x: Array[Double] => new ofDouble
      case x: Array[Unit] => new ofUnit
      case x: Array[AnyRef] => new ofRef[AnyRef]
    }).asInstanceOf[AtomicArrayBuilder[T]]
  }

  private val EmptyIntArray = new Array[Int](0)
  private val EmptyLongArray = new Array[Long](0)
  private val EmptyRefArray = new Array[AnyRef](0)

  abstract class IntBacked[T] extends AtomicArrayBuilder[T] {
    protected var elems = EmptyIntArray
    protected var size: Int = 0

    protected def setCapacity(newCap: Int) {
      if (newCap != elems.length) {
        val newElems = new Array[Int](newCap)
        if (size > 0) Array.copy(elems, 0, newElems, 0, size)
        elems = newElems
      }
    }

    override def sizeHint(sizeHint: Int) {
      if (elems.length < sizeHint) setCapacity(sizeHint)
    }

    protected def ensureSpace() {
      val cap = elems.length
      if (size == cap) setCapacity(if (cap == 0) 16 else cap * 2)
    }

    def clear() {
      size = 0
    }
  }

  abstract class LongBacked[T] extends AtomicArrayBuilder[T] {
    protected var elems = EmptyLongArray
    protected var size: Int = 0

    protected def setCapacity(newCap: Int) {
      if (newCap != elems.length) {
        val newElems = new Array[Long](newCap)
        if (size > 0) Array.copy(elems, 0, newElems, 0, size)
        elems = newElems
      }
    }

    override def sizeHint(sizeHint: Int) {
      if (elems.length < sizeHint) setCapacity(sizeHint)
    }

    protected def ensureSpace() {
      val cap = elems.length
      if (size == cap) setCapacity(if (cap == 0) 16 else cap * 2)
    }

    def clear() {
      size = 0
    }
  }


  class ofBoolean extends IntBacked[Boolean] {
    def +=(elem: Boolean): this.type = {
      ensureSpace()
      elems(size) = if (elem) 1 else 0
      size += 1
      this
    }

    def result(): AtomicArray[Boolean] = {
      setCapacity(size)
      new AtomicArray.ofBoolean(new AtomicIntegerArray(elems))
    }
  }

  class ofByte extends IntBacked[Byte] {
    def +=(elem: Byte): this.type = {
      ensureSpace()
      elems(size) = elem
      size += 1
      this
    }

    def result(): AtomicArray[Byte] = {
      setCapacity(size)
      new AtomicArray.ofByte(new AtomicIntegerArray(elems))
    }
  }

  class ofShort extends IntBacked[Short] {
    def +=(elem: Short): this.type = {
      ensureSpace()
      elems(size) = elem
      size += 1
      this
    }

    def result(): AtomicArray[Short] = {
      setCapacity(size)
      new AtomicArray.ofShort(new AtomicIntegerArray(elems))
    }
  }

  class ofChar extends IntBacked[Char] {
    def +=(elem: Char): this.type = {
      ensureSpace()
      elems(size) = elem
      size += 1
      this
    }

    def result(): AtomicArray[Char] = {
      setCapacity(size)
      new AtomicArray.ofChar(new AtomicIntegerArray(elems))
    }
  }

  class ofInt extends IntBacked[Int] {
    def +=(elem: Int): this.type = {
      ensureSpace()
      elems(size) = elem
      size += 1
      this
    }

    def result(): AtomicArray[Int] = {
      setCapacity(size)
      new AtomicArray.ofInt(new AtomicIntegerArray(elems))
    }
  }

  class ofFloat extends IntBacked[Float] {
    def +=(elem: Float): this.type = {
      ensureSpace()
      elems(size) = java.lang.Float.floatToRawIntBits(elem)
      size += 1
      this
    }

    def result(): AtomicArray[Float] = {
      setCapacity(size)
      new AtomicArray.ofFloat(new AtomicIntegerArray(elems))
    }
  }

  class ofLong extends LongBacked[Long] {
    def +=(elem: Long): this.type = {
      ensureSpace()
      elems(size) = elem
      size += 1
      this
    }

    def result(): AtomicArray[Long] = {
      setCapacity(size)
      new AtomicArray.ofLong(new AtomicLongArray(elems))
    }
  }

  class ofDouble extends LongBacked[Double] {
    def +=(elem: Double): this.type = {
      ensureSpace()
      elems(size) = java.lang.Double.doubleToRawLongBits(elem)
      size += 1
      this
    }

    def result(): AtomicArray[Double] = {
      setCapacity(size)
      new AtomicArray.ofDouble(new AtomicLongArray(elems))
    }
  }

  class ofUnit extends AtomicArrayBuilder[Unit] {
    protected var size = 0

    def clear(): Unit = { size = 0 }
    def +=(elem: Unit): this.type = { size += 1; this }
    def result(): AtomicArray[Unit] = new AtomicArray.ofUnit(size)
  }

  class ofRef[T <: AnyRef] extends AtomicArrayBuilder[T] {
    protected var elems = EmptyRefArray
    protected var size: Int = 0

    protected def setCapacity(newCap: Int) {
      if (newCap != elems.length) {
        val newElems = new Array[AnyRef](newCap)
        if (size > 0) Array.copy(elems, 0, newElems, 0, size)
        elems = newElems
      }
    }

    override def sizeHint(sizeHint: Int) {
      if (elems.length < sizeHint) setCapacity(sizeHint)
    }

    protected def ensureSpace() {
      val cap = elems.length
      if (size == cap) setCapacity(if (cap == 0) 16 else cap * 2)
    }

    def clear() {
      size = 0
    }

    def +=(elem: T): this.type = {
      ensureSpace()
      elems(size) = elem
      size += 1
      this
    }

    def result(): AtomicArray[T] = {
      setCapacity(size)
      new AtomicArray.ofRef(new AtomicReferenceArray[AnyRef](elems).asInstanceOf[AtomicReferenceArray[T]])
    }
  }
}
