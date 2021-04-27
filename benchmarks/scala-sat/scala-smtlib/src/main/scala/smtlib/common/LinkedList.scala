package smtlib.common

/*
 * Mutable data structure with O(1) append and prepend as
 * well as pop operation.
 */
class LinkedList[T] {

  private class Node(val el: T, var next: Node)

  private var _head: Node = null
  private var _last: Node = null

  def append(el: T): Unit = {
    if(_head == null) {
      _head = new Node(el, null)
      _last = _head
    } else {
      val previousLast = _last
      _last = new Node(el, null)
      previousLast.next = _last
    }
  }

  def prepend(el: T): Unit = {
    if(_head == null) {
      _head = new Node(el, null)
      _last = _head
    } else {
      _head = new Node(el, _head)
    }
  }

  def pop(): T = {
    val firstElem = _head.el
    if(_head.next == null) {
      _head = null
      _last = null
    } else {
      _head = _head.next
    }
    firstElem
  }

  def size: Int = {
    var res = 0
    var headPtr = _head
    while(headPtr != null) {
      res += 1
      headPtr = headPtr.next
    }
    res
  }

  def isEmpty: Boolean = _head == null

}
