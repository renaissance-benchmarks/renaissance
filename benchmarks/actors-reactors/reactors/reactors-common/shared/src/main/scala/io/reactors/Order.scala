package io.reactors






/** Specialized typeclass for describing ordering between elements.
 */
trait Order[@specialized(Short, Int, Long, Float, Double) T] {

  def compare(x: T, y: T): Int

  def lteq(x: T, y: T) = compare(x, y) <= 0

  def gteq(x: T, y: T) = compare(x, y) >= 0

  def lt(x: T, y: T) = compare(x, y) < 0

  def gt(x: T, y: T) = compare(x, y) > 0

  def equiv(x: T, y: T) = compare(x, y) == 0

}


/** Default ordering objects.
 */
object Order {

  def apply[@specialized(Short, Int, Long, Float, Double) T](f: (T, T) => Int) =
    new Order[T] {
      def compare(x: T, y: T): Int = f(x, y)
    }

  def double[@specialized(Short, Int, Long, Float, Double) T](f: (T, T) => Double) =
    new Order[T] {
      def compare(x: T, y: T): Int = {
        val diff = f(x, y)
        if (diff < 0.0) -1
        else if (diff > 0.0) 1
        else 0
      }
    }

  implicit object ShortOrder extends Order[Short] {
    def compare(x: Short, y: Short) =
      if (x < y) -1
      else if (x == y) 0
      else 1
  }

  implicit object IntOrder extends Order[Int] {
    def compare(x: Int, y: Int) =
      if (x < y) -1
      else if (x == y) 0
      else 1
  }

  implicit object LongOrder extends Order[Long] {
    def compare(x: Long, y: Long) =
      if (x < y) -1
      else if (x == y) 0
      else 1
  }

  implicit object FloatOrder extends Order[Float] {
    def compare(x: Float, y: Float) =
      if (x < y) -1
      else if (x == y) 0
      else 1
  }

  implicit object DoubleOrder extends Order[Double] {
    def compare(x: Double, y: Double) =
      if (x < y) -1
      else if (x == y) 0
      else 1
  }

  implicit def fromOrdering[T <: AnyRef: Ordering] = new Order[T] {
    val ordering = implicitly[Ordering[T]]
    def compare(x: T, y: T) = ordering.compare(x, y)
  }

}
