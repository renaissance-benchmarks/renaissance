package io.reactors
package common






class BinaryHeap[@specialized(Int, Long, Double) T](val initialSize: Int = 16)(
  implicit val arrayable: Arrayable[T], val order: Order[T]
) {
  private var array: Array[T] = _
  private var sz = 0

  private def init(dummy: BinaryHeap[T]) {
    array = arrayable.newRawArray(initialSize)
    sz = 0
  }

  init(this)

  private def fixUp(arr: Array[T], from: Int) {
    var pos = from
    while (pos > 1 && order.gt(arr(pos / 2), arr(pos))) {
      val tmp = arr(pos)
      arr(pos) = arr(pos / 2)
      arr(pos / 2) = tmp
      pos = pos / 2
    }
  }

  private def fixDown(arr: Array[T], from: Int, to: Int) {
    var pos = from
    val arr = array
    while (2 * pos <= to) {
      var childpos = 2 * pos
      if (childpos < to && order.gt(arr(childpos), arr(childpos + 1))) childpos += 1

      if (order.lteq(arr(pos), arr(childpos))) {
        pos = to + 1
      } else {
        val tmp = arr(pos)
        arr(pos) = arr(childpos)
        arr(childpos) = tmp
        pos = childpos
      }
    }
  }

  private def grow(dummy: BinaryHeap[T]) {
    val narray = arrayable.newRawArray(array.size * 2)
    System.arraycopy(array, 1, narray, 1, sz)
    array = narray
  }

  def enqueue(elem: T) = {
    if (sz == array.length - 1) grow(this)
    array(sz + 1) = elem
    sz += 1
    fixUp(array, sz)
  }

  def dequeue(): T = {
    if (sz > 0) {
      val elem = array(1)
      array(1) = array(sz)
      array(sz) = arrayable.nil
      sz -= 1
      fixDown(array, 1, sz)
      elem
    } else throw new NoSuchElementException("empty")
  }

  def head: T = {
    if (sz > 0) array(1)
    else throw new NoSuchElementException("empty")
  }

  def size: Int = sz

  def isEmpty = sz == 0

  def nonEmpty = !isEmpty

  def foreach(f: T => Unit): Unit = {
    var i = 1
    while (i <= sz) {
      f(array(i))
      i += 1
    }
  }

  def clear() {
    array = arrayable.newArray(initialSize)
    sz = 0
  }

  def toArray: Array[T] = {
    val result = arrayable.newRawArray(sz)
    var i = 1
    while (i <= sz) {
      result(i - 1) = array(i)
      i += 1
    }
    result
  }

  private[common] def debugString = s"Heap(sz: $sz, array: ${array.mkString(", ")})"

}


object BinaryHeap {

  def orderedWith[@specialized(Int, Long, Double) T: Arrayable]
    (initSize: Int = 16, ord: Order[T]) =
    new BinaryHeap(initSize)(implicitly[Arrayable[T]], ord)

}
