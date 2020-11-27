package smtlib.common

import org.scalatest.funsuite.AnyFunSuite

class LinkedListTests extends AnyFunSuite {


  test("append one element on empty list pop the same element") {
    val l = new LinkedList[Int]
    l.append(3)
    assert(l.pop() === 3)
  }

  test("multiple appends pop in same order") {
    val l = new LinkedList[Int]
    l.append(2)
    l.append(3)
    l.append(1)
    assert(l.pop() === 2)
    assert(l.pop() === 3)
    assert(l.pop() === 1)
  }

  test("append with same element does duplicate the element") {
    val l = new LinkedList[Int]
    l.append(2)
    l.append(2)
    l.append(1)
    assert(l.pop() === 2)
    assert(l.pop() === 2)
    assert(l.pop() === 1)
  }

  test("mixing appends and pops work as expected") {
    val l = new LinkedList[Int]
    l.append(2)
    l.append(3)
    assert(l.pop() === 2)
    l.append(1)
    assert(l.pop() === 3)
    l.append(0)
    assert(l.pop() === 1)
    assert(l.pop() === 0)
  }

  test("prepend one element on empty list pop the same element") {
    val l = new LinkedList[Int]
    l.prepend(3)
    assert(l.pop() === 3)
  }

  test("multiple preprends pop in reverse order") {
    val l = new LinkedList[Int]
    l.prepend(2)
    l.prepend(3)
    l.prepend(1)
    assert(l.pop() === 1)
    assert(l.pop() === 3)
    assert(l.pop() === 2)
  }

  test("prepend with same element does duplicate the element") {
    val l = new LinkedList[Int]
    l.prepend(2)
    l.prepend(2)
    l.prepend(1)
    assert(l.pop() === 1)
    assert(l.pop() === 2)
    assert(l.pop() === 2)
  }

  test("mixing prepends and pops work as expected") {
    val l = new LinkedList[Int]
    l.prepend(2)
    l.prepend(3)
    assert(l.pop() === 3)
    l.prepend(1)
    assert(l.pop() === 1)
    l.prepend(0)
    assert(l.pop() === 0)
    assert(l.pop() === 2)
  }

  test("mixing prepends, appends and pops work as expected") {
    val l = new LinkedList[Int]
    l.append(42)
    l.append(22)
    l.prepend(2)
    l.prepend(3)
    l.append(12)
    assert(l.pop() === 3)
    l.prepend(10)
    l.append(17)
    assert(l.pop() === 10)
    assert(l.pop() === 2)
    assert(l.pop() === 42)
    assert(l.pop() === 22)
    l.append(7)
    assert(l.pop() === 12)
    assert(l.pop() === 17)
    assert(l.pop() === 7)
  }

  test("size of empty list is 0") {
    val l = new LinkedList[Int]
    assert(l.size === 0)
  }

  test("size of list of 1 element is 1") {
    val l = new LinkedList[Int]
    l.append(21)
    assert(l.size === 1)
  }

  test("size of list of 2 elements is 2") {
    val l = new LinkedList[Int]
    l.append(21)
    l.append(11)
    assert(l.size === 2)
  }

  test("size is consistent with appends and pops") {
    val l = new LinkedList[Int]
    assert(l.size === 0)
    l.append(21)
    assert(l.size === 1)
    l.pop()
    assert(l.size === 0)
    l.append(11)
    l.append(42)
    assert(l.size === 2)
    l.pop()
    assert(l.size === 1)
  }

  test("isEmpty returns true with newly created list") {
    val l = new LinkedList[Int]
    assert(l.isEmpty)
  }
  test("isEmpty returns false with one append") {
    val l = new LinkedList[Int]
    l.append(1)
    assert(!l.isEmpty)
  }
  test("isEmpty returns false with one prepend") {
    val l = new LinkedList[Int]
    l.prepend(1)
    assert(!l.isEmpty)
  }
  test("isEmpty returns true if enough pop make the list empty again") {
    val l = new LinkedList[Int]
    l.prepend(1)
    l.pop()
    assert(l.isEmpty)
  }

  test("isEmpty is not true after a single pop that does not make the list empty") {
    val l = new LinkedList[Int]
    l.append(2)
    l.prepend(3)
    assert(!l.isEmpty)
    l.pop()
    assert(!l.isEmpty)
  }
  test("isEmpty is eventually true after enough pops") {
    val l = new LinkedList[Int]
    l.append(2)
    l.prepend(3)
    l.append(4)
    assert(!l.isEmpty)
    l.pop()
    l.pop()
    l.pop()
    assert(l.isEmpty)
  }
}
