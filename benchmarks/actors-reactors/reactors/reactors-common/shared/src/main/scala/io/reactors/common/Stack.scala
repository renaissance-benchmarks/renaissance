package io.reactors.common



import io.reactors._



class Stack[@specialized(Int, Long, Double) T: Arrayable] {
  private var array: Array[T] = _
  private var pos: Int = _

  def init(s: Stack[T]): Unit = {
    array = implicitly[Arrayable[T]].newRawArray(4)
    pos = -1
  }
  init(this)

  def push(x: T): Unit = {
    pos += 1
    if (pos >= array.length) upsize(implicitly[Arrayable[T]])
    array(pos) = x
  }

  private def upsize(a: Arrayable[T]): Unit = {
    val narray = a.newRawArray(array.size * 2)
    System.arraycopy(array, 0, narray, 0, array.length)
    array = narray
  }

  def pop(): T = {
    if (pos < 0) sys.error("<empty>.pop")
    val x = array(pos)
    pos -= 1
    x
  }

  def peek: T = {
    if (pos < 0) sys.error("<empty>.pop")
    array(pos)
  }

  def size: Int = pos + 1

  def isEmpty: Boolean = size == 0

  def nonEmpty: Boolean = !isEmpty
}
