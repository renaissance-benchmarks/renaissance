package cafesat.sat

import org.scalatest.FunSuite

class EvalSuite extends FunSuite {

  private val l1 = new Literal(0, true)
  private val l2 = new Literal(0, false)
  private val l3 = new Literal(1, true)
  private val l4 = new Literal(1, false)
  private val l5 = new Literal(2, true)
  private val l6 = new Literal(2, false)

  private val c1 = Set(l1, l3, l5)
  private val c2 = Set(l2, l4, l6)
  private val c3 = Set(l1, l4)
  private val c4 = Set(l2, l5)

  test("Eval of no clause should be true") {
    assert(Eval(Set(), Array()) === true)
  }

  test("Eval works with one literal") {
    assert(Eval(Set(Set(l1)), Array(true)) === true)
    assert(Eval(Set(Set(l1)), Array(false)) === false)
  }

  test("Eval works with one clause") {
    assert(Eval(Set(c1), Array(false, false, false)) === false)
    assert(Eval(Set(c1), Array(true, false, false)) === true)
  }

  test("Eval works with set of clauses") {
    assert(Eval(Set(c1, c2), Array(true, true, true)) === false)
    assert(Eval(Set(c1, c2), Array(true, false, true)) === true)
    assert(Eval(Set(c1, c2), Array(true, true, false)) === true)
    assert(Eval(Set(c1, c2), Array(false, false, false)) === false)

    assert(Eval(Set(c1, c3, c4), Array(true, false, true)) === true)
    assert(Eval(Set(c1, c3, c4), Array(true, false, false)) === false)

    assert(Eval(Set(c2, c3, c4), Array(false, false, true)) === true)
    assert(Eval(Set(c2, c3, c4), Array(false, true, true)) === false)
  }

}
