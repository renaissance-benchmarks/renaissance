package io.reactors.common



import io.reactors.Arrayable



class ArrayRing[@specialized(Int, Long, Double) T: Arrayable](val window: Int = -1) {
  private[reactors] var array: Array[T] = _
  private[reactors] var firstIdx: Int = _
  private[reactors] var lastIdx: Int = _

  def init(self: ArrayRing[T]): Unit = {
    if (window != -1) {
      array = implicitly[Arrayable[T]].newRawArray(window + 1)
    } else {
      array = implicitly[Arrayable[T]].newRawArray(5)
    }
    firstIdx = 0
    lastIdx = 0
  }

  init(this)

  def apply(idx: Int): T = {
    if (idx < 0 || idx >= size) throw new IndexOutOfBoundsException(idx.toString)
    array((firstIdx + idx) % array.length)
  }

  def head: T = apply(0)

  def last: T = apply(size - 1)

  def resize(): Unit = {
    val narray = implicitly[Arrayable[T]].newRawArray(array.length * 2 + 1)
    var i = 0
    val sz = size
    while (i < sz) {
      narray(i) = apply(i)
      i += 1
    }
    array = narray
    firstIdx = 0
    lastIdx = i
  }

  def enqueue(x: T): Unit = {
    if (size == array.length - 1) {
      if (window != -1) throw new IllegalStateException("<full>.enqueue")
      else resize()
    }
    array(lastIdx) = x
    lastIdx = (lastIdx + 1) % array.length
  }

  def dequeue(): T = {
    if (size == 0) throw new IllegalStateException("<empty>.dequeue")
    val x = array(firstIdx)
    array(firstIdx) = implicitly[Arrayable[T]].nil
    firstIdx = (firstIdx + 1) % array.length
    x
  }

  def dequeueMany(n: Int): Unit = {
    if (n > size) throw new IllegalStateException(s"<size=$size>.dequeueMany($n)")
    var left = n
    while (left > 0) {
      dequeue()
      left -= 1
    }
  }

  protected def rawClear(self: ArrayRing[T]): Unit = {
    var i = 0
    val nil = implicitly[Arrayable[T]].nil
    while (i < array.length) {
      array(i) = nil
      i += 1
    }
    firstIdx = 0
    lastIdx = 0
  }

  def clear(): Unit = rawClear(this)

  def size: Int = (lastIdx + array.length - firstIdx) % array.length

  def isEmpty: Boolean = size == 0

  def nonEmpty: Boolean = !isEmpty
}
