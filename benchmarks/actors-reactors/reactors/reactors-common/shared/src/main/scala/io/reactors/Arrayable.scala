package io.reactors



import scala.reflect.ClassTag



/** A typeclass that describes how to instantiate an array for the given type `T`.
 *  
 *  This is a class tag on steroids.
 *  It is used in reactive containers that have to do a lot of array allocations.
 * 
 *  @tparam T       type for which we want to instantiate an array
 */
trait Arrayable[@specialized(Byte, Short, Int, Float, Long, Double) T]
extends Serializable {
  /** Class tag for type `T`.
   */
  val classTag: ClassTag[T]

  /** Returns the `nil` value for the type -- a value never
   *  used by user applications.
   * 
   *  For reference types this is usually `null`,
   *  but for integers this will usually be `Int.MinValue`
   *  and not `0`.
   */
  val nil: T

  /** Creates an array of type `T` initialized with `nil`.
   */
  def newArray(sz: Int): Array[T]

  /** Creates an array of type `T` initialized with the default JVM value for that type.
   */
  def newRawArray(sz: Int): Array[T]

  /** Reads from an array entry.
   */
  def apply(array: Array[T], idx: Int): T

  /** Writes to an array entry.
   */
  def update(array: Array[T], idx: Int, v: T): Unit

  /** Returns a new arrayable with an alternative nil.
   */
  def withNil(n: T) = new Arrayable.WithNil(this, classTag, n)
}


/** Contains `Arrayable` typeclasses which have a low priority
 *  and are selected only if there is no `Arrayable` for a more specific type.
 */
trait LowPriorityArrayableImplicits {
  implicit def any[T: ClassTag]: Arrayable[T] = new Arrayable[T] {
    val classTag = implicitly[ClassTag[T]]
    val nil = null.asInstanceOf[T]
    def newArray(sz: Int) = new Array[T](sz)
    def newRawArray(sz: Int) = newArray(sz)
    def apply(array: Array[T], idx: Int): T = array(idx)
    def update(array: Array[T], idx: Int, v: T): Unit = array(idx) = v
  }
}


/** Contains default `Arrayable` typeclasses.
 */
object Arrayable extends LowPriorityArrayableImplicits {

  class WithNil[@specialized(Byte, Short, Int, Float, Long, Double) T](
    val arrayable: Arrayable[T],
    val classTag: ClassTag[T],
    val nil: T
  ) extends Arrayable[T] {
    def newArray(sz: Int) = {
      val a = arrayable.newRawArray(sz)
      var i = 0
      while (i < sz) {
        a(i) = nil
        i += 1
      }
      a
    }
    def newRawArray(sz: Int) = arrayable.newRawArray(sz)
    def apply(array: Array[T], idx: Int) = arrayable.apply(array, idx)
    def update(array: Array[T], idx: Int, v: T) = arrayable.update(array, idx, v)
  }

  implicit def ref[T >: Null <: AnyRef: ClassTag]: Arrayable[T] = new Arrayable[T] {
    val classTag = implicitly[ClassTag[T]]
    val nil = null
    def newArray(sz: Int) = new Array[T](sz)
    def newRawArray(sz: Int) = newArray(sz)
    def apply(array: Array[T], idx: Int): T = array(idx)
    def update(array: Array[T], idx: Int, v: T): Unit = array(idx) = v
  }

  implicit val long: Arrayable[Long] = new Arrayable[Long] {
    val classTag = implicitly[ClassTag[Long]]
    val nil = Long.MinValue
    def newArray(sz: Int) = {
      val a = new Array[Long](sz)
      var i = 0
      while (i < sz) {
        a(i) = nil
        i += 1
      }
      a
    }
    def newRawArray(sz: Int) = new Array[Long](sz)
    def apply(array: Array[Long], idx: Int): Long = array(idx)
    def update(array: Array[Long], idx: Int, v: Long): Unit = array(idx) = v
  }

  implicit val double: Arrayable[Double] = new Arrayable[Double] {
    val classTag = implicitly[ClassTag[Double]]
    val nil = Double.NegativeInfinity
    def newArray(sz: Int) = {
      val a = new Array[Double](sz)
      var i = 0
      while (i < sz) {
        a(i) = nil
        i += 1
      }
      a
    }
    def newRawArray(sz: Int) = new Array[Double](sz)
    def apply(array: Array[Double], idx: Int): Double = array(idx)
    def update(array: Array[Double], idx: Int, v: Double): Unit = array(idx) = v
  }

  implicit val float: Arrayable[Float] = new Arrayable[Float] {
    val classTag = implicitly[ClassTag[Float]]
    val nil = Float.NaN
    def newArray(sz: Int) = {
      val a = new Array[Float](sz)
      var i = 0
      while (i < sz) {
        a(i) = nil
        i += 1
      }
      a
    }
    def newRawArray(sz: Int) = new Array[Float](sz)
    def apply(array: Array[Float], idx: Int): Float = array(idx)
    def update(array: Array[Float], idx: Int, v: Float): Unit = array(idx) = v
  }

  implicit val int: Arrayable[Int] = new Arrayable[Int] {
    val classTag = implicitly[ClassTag[Int]]
    val nil = Int.MinValue
    def newArray(sz: Int) = {
      val a = new Array[Int](sz)
      var i = 0
      while (i < sz) {
        a(i) = nil
        i += 1
      }
      a
    }
    def newRawArray(sz: Int) = new Array[Int](sz)
    def apply(array: Array[Int], idx: Int): Int = array(idx)
    def update(array: Array[Int], idx: Int, v: Int): Unit = array(idx) = v
  }

  val nonZeroInt: Arrayable[Int] = new Arrayable[Int] {
    val classTag = implicitly[ClassTag[Int]]
    val nil = 0
    def newArray(sz: Int) = newRawArray(sz)
    def newRawArray(sz: Int) = new Array[Int](sz)
    def apply(array: Array[Int], idx: Int): Int = array(idx)
    def update(array: Array[Int], idx: Int, v: Int): Unit = array(idx) = v
  }

  implicit val short: Arrayable[Short] = new Arrayable[Short] {
    val classTag = implicitly[ClassTag[Short]]
    val nil = Short.MinValue
    def newArray(sz: Int) = {
      val a = new Array[Short](sz)
      var i = 0
      while (i < sz) {
        a(i) = nil
        i += 1
      }
      a
    }
    def newRawArray(sz: Int) = new Array[Short](sz)
    def apply(array: Array[Short], idx: Int): Short = array(idx)
    def update(array: Array[Short], idx: Int, v: Short): Unit = array(idx) = v
  }

  implicit val byte: Arrayable[Byte] = new Arrayable[Byte] {
    val classTag = implicitly[ClassTag[Byte]]
    val nil = Byte.MinValue
    def newArray(sz: Int) = {
      val a = new Array[Byte](sz)
      var i = 0
      while (i < sz) {
        a(i) = nil
        i += 1
      }
      a
    }
    def newRawArray(sz: Int) = new Array[Byte](sz)
    def apply(array: Array[Byte], idx: Int): Byte = array(idx)
    def update(array: Array[Byte], idx: Int, v: Byte): Unit = array(idx) = v
  }

}
