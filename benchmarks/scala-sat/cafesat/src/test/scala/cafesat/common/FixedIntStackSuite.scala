package cafesat.common

import org.scalatest.FunSuite

class FixedIntStackSuite extends FunSuite {

  test("a new stack is empty") {
    val s = new FixedIntStack(5)
    assert(s.isEmpty)
    assert(s.size === 0)
  }

  test("pushing on empty stack contains exactly that element") {
    val s = new FixedIntStack(5)
    s.push(42)
    assert(s.size === 1)
    assert(s.top === 42)
  }

  test("pop returns last pushed element") {
    val s = new FixedIntStack(5)
    s.push(17)
    assert(s.pop() === 17)
  }

  test("stack behaves in LIFO") {
    val s = new FixedIntStack(5)
    s.push(17)
    s.push(18)
    s.push(19)
    assert(s.pop() === 19)
    assert(s.pop() === 18)
    s.push(42)
    assert(s.pop() === 42)
    assert(s.pop() === 17)
  }

  test("size growths with each push") {
    val s = new FixedIntStack(5)
    assert(s.size === 0)
    s.push(17)
    assert(s.size === 1)
    s.push(18)
    assert(s.size === 2)
    s.push(19)
    assert(s.size === 3)
  }

  test("size shrinks with each pop") {
    val s = new FixedIntStack(5)
    s.push(1)
    s.push(2)
    s.push(3)
    assert(s.size === 3)
    s.pop()
    assert(s.size === 2)
    s.pop()
    assert(s.size === 1)
    s.pop()
    assert(s.size === 0)
  }

}
