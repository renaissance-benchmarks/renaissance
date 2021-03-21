package io.reactors
package common



import scala.annotation.tailrec
import scala.collection._



class UnrolledRing[@specialized(Byte, Short, Int, Float, Long, Double) T](
  implicit val arrayable: Arrayable[T]
) {
  import UnrolledRing._

  private[reactors] var start: Node[T] = _
  private[reactors] var end: Node[T] = _
  private[reactors] var rawSize: Int = _

  private[reactors] def init(a: Arrayable[T]) {
    start = new Node(arrayable.newRawArray(INITIAL_NODE_LENGTH), 0, 0)
    start.next = start
    end = start
    rawSize = 0
  }

  init(arrayable)

  private[reactors] final def advance() {
    if (start.isEmpty && start.next.nonEmpty && start != end) {
      start.reset()
      start = start.next
    }
  }

  def clear() {
    init(arrayable)
  }

  def size: Int = rawSize

  def nonEmpty: Boolean = {
    if (start.nonEmpty) true
    else {
      advance()
      start.nonEmpty
    }
  }

  def isEmpty: Boolean = !nonEmpty

  def head: T = {
    if (nonEmpty) start.head
    else throw new NoSuchElementException("empty")
  }

  def enqueue(elem: T) {
    end.enqueue(this, elem)
    rawSize += 1
  }

  def dequeue(): T = {
    advance()
    val elem = start.dequeue(this)
    rawSize -= 1
    elem
  }

  def remove(elem: T): Int = {
    val at = UnrolledRing.remove(this, null, start, elem, 0)
    if (at != -1) rawSize -= 1
    at
  }

  def foreach(f: T => Unit) {
    @tailrec def foreach(n: Node[T]) {
      val array = n.array
      var i = n.start
      while (i < n.until) {
        f(array(i))
        i += 1
      }
      if (n != end) foreach(n.next)
    }
    foreach(start)
  }

  private[reactors] def nodes: Seq[Node[T]] = {
    var curr = start
    val buffer = mutable.Buffer[Node[T]]()
    do {
      buffer += curr
      curr = curr.next
    } while (curr != end)
    buffer
  }

  def debugString = {
    var chain = ""
    var n = start
    do {
      var ptr = ""
      if (n == start) ptr += "$"
      if (n == end) ptr += "^"
      chain += s"$ptr[${n.start}, ${n.until}: ${n.array.mkString(", ")}] --> "
      n = n.next
    } while (n != start)
    s"UnrolledRing($chain)"
  }

}


object UnrolledRing {

  val INITIAL_NODE_LENGTH = 8
  val MAXIMUM_NODE_LENGTH = 128

  class Node[@specialized(Byte, Short, Int, Float, Long, Double) T](
    val array: Array[T], var start: Int, var until: Int
  ) {
    var next: Node[T] = null

    final def isEmpty = start == until

    final def nonEmpty = !isEmpty

    def head = array(start)

    def reset() {
      start = 0
      until = 0
    }

    private def reserve(ring: UnrolledRing[T]) {
      val nextlen = math.min(MAXIMUM_NODE_LENGTH, array.length * 4)
      val fresh = new Node[T](ring.arrayable.newRawArray(nextlen), 0, 0)
      fresh.next = this.next
      this.next = fresh
      ring.end = fresh
    }

    def enqueue(ring: UnrolledRing[T], elem: T) {
      if (until < array.length) {
        array(until) = elem
        until += 1
        // TODO(axel22): This prematurely allocates without checking. Fix, and add
        // ScalaMeter tests for boxing.
        if (until == array.length) {
          if (this.isEmpty) {
            this.reset()
          } else if (next.isEmpty && next.start == 0) {
            next.reset()
            ring.end = next
          } else {
            reserve(ring)
          }
        }
      } else if (this.isEmpty) {
        this.reset()
        this.enqueue(ring, elem)
      } else if (next.isEmpty) {
        next.reset()
        next.enqueue(ring, elem)
        ring.end = next
      } else {
        reserve(ring)
        this.next.enqueue(ring, elem)
      }
    }

    def dequeue(ring: UnrolledRing[T]): T = {
      if (isEmpty) throw new NoSuchElementException("empty")

      val elem = array(start)
      array(start) = null.asInstanceOf[T]
      start += 1
      elem
    }
  }

  @tailrec final def remove[@specialized(Byte, Short, Int, Float, Long, Double) T](
    ring: UnrolledRing[T], prev: Node[T], curr: Node[T], elem: T, at: Int
  ): Int = {
    var position = -1

    //println(
    //  s"rem $elem in ${curr.array.mkString(", ")}::: ${curr.start}, ${curr.until}")
    var i = curr.start
    while (i < curr.until) {
      if (curr.array(i) == elem) {
        position = i
        i = curr.until
      } else i += 1
    }

    //println(s"position: $position")
    if (position != -1) {
      var j = position + 1
      while (j < curr.until) {
        curr.array(j - 1) = curr.array(j)
        j += 1
      }
      curr.until -= 1
      curr.array(curr.until) = null.asInstanceOf[T]

      // check if the node is completely empty
      if (curr.start == curr.until) {
        if (curr.next ne curr) {
          // there are at least 2 nodes
          if (prev == null) {
            // remove start node
            ring.end.next = curr.next
            ring.start = curr.next
          } else {
            prev.next = curr.next
            if (curr == ring.end) ring.end = prev
          }
        }
      }

      at + position
    } else if (curr == ring.end) -1
    else remove(ring, curr, curr.next, elem, at + curr.until - curr.start)
  }

}
