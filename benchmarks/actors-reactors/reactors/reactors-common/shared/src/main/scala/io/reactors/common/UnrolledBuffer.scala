package io.reactors
package common



import scala.annotation.tailrec



class UnrolledBuffer[@specialized(Int, Long, Double) T](
  implicit val arrayable: Arrayable[T]
) {
  import UnrolledBuffer._

  private[reactors] var start: Node[T] = _
    
  private[reactors] var rawEnd: Node[T] = _

  def end: Node[T] = rawEnd

  def end_=(n: Node[T]) = rawEnd = n

  def init(self: UnrolledBuffer[T]) {
    start = new Node[T](this, arrayable.newRawArray(INITIAL_NODE_LENGTH))
    end = start
  }

  init(this)

  def isEmpty = !nonEmpty

  @tailrec private def advance() {
    if (start.startIndex >= start.endIndex) {
      if (start.next != null) {
        val old = start
        start = start.next
        old.next = null
        advance()
      }
    }
  }

  def nonEmpty = {
    advance()
    start.startIndex < start.endIndex
  }

  def head: T = {
    if (nonEmpty) start.array(start.startIndex)
    else throw new NoSuchElementException("empty")
  }

  def dequeue(): T = {
    if (isEmpty) throw new NoSuchElementException("empty")
    val array = start.array
    val si = start.startIndex
    val elem = array(si)
    array(si) = arrayable.nil
    start.startIndex += 1
    elem
  }

  def enqueue(elem: T) = this += elem

  def +=(elem: T): this.type = {
    end += elem
    this
  }

  def foreach(f: T => Unit) {
    var node = start
    while (node != null) {
      var i = node.startIndex
      val array = node.array
      val until = node.endIndex
      while (i < until) {
        f(array(i))
        i += 1
      }
      node = node.next
    }
  }

  def newNode: Node[T] = new Node[T](this, arrayable.newRawArray(INITIAL_NODE_LENGTH))

  def clear() {
    start = newNode
    end = start
  }
}


object UnrolledBuffer {

  def INITIAL_NODE_LENGTH = 8
  def MAXIMUM_NODE_LENGTH = 128

  class Node[@specialized(Int, Long, Double) T](
    val outer: UnrolledBuffer[T], val array: Array[T]
  ) {
    private[reactors] var startIndex = 0
    private[reactors] var endIndex = 0
    private[reactors] var rawNext: Node[T] = null

    def next: Node[T] = rawNext

    def next_=(n: Node[T]) = rawNext = n

    def +=(elem: T) {
      if (endIndex < array.length) {
        array(endIndex) = elem
        endIndex += 1
      } else {
        val nlen = math.min(MAXIMUM_NODE_LENGTH, array.length * 2)
        next = new Node(outer, outer.arrayable.newRawArray(nlen))
        outer.end = next
        next += elem
      }
    }
  }

}