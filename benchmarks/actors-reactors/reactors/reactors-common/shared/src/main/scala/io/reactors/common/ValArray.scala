package io.reactors.common



import scala.reflect.ClassTag



class ValArray[@specialized(Byte, Char, Int, Long, Float, Double) T: ClassTag](
  private var raw: Array[T]
) {
  def this(len: Int) = this(new Array[T](len))

  def apply(i: Int): T = raw(i)

  def length: Int = raw.length
}


object ValArray {
}
