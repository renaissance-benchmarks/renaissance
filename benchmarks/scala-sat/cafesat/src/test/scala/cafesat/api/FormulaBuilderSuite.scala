package cafesat.api

import FormulaBuilder._
import Solver._

import org.scalatest.FunSuite


class FormulaBuilderSuite extends FunSuite {

  private val x1 = propVar()
  private val x2 = propVar()
  private val x3 = propVar()

  test("Simple variable is solved to be true") {
    val result = solveForSatisfiability(x1)
    assert(result !== None)
    result.foreach(m => {
      assert(m(x1))
    })
  }

  test("Negation of formulas are properly solved") {
    val result = solveForSatisfiability(!x1)
    assert(result !== None)
    result.foreach(m => {
      assert(!m(x1))
    })
  }

  test("Conjunction of formulas are properly solved") {
    val f1 = x1 && x2 && x3
    val result = solveForSatisfiability(f1)
    assert(result !== None)
    result.foreach(m => {
      assert(m(x1))
      assert(m(x2))
      assert(m(x3))
    })
  }

  test("Disjunction of formulas are properly solved") {
    val f1 = x1 || x2 || x3
    val result = solveForSatisfiability(f1)
    assert(result !== None)
    result.foreach(m => {
      assert(m(x1) || m(x2) || m(x3))
    })
  }

  test("All variables in the formula are mapped in the model") {
    val f1 = x1 && (x2 || x3)
    val result = solveForSatisfiability(f1)
    assert(result !== None)
    result.foreach(m => {
      assert(m.isDefinedAt(x1))
      assert(m.isDefinedAt(x2))
      assert(m.isDefinedAt(x3))
    })
  }

  test("Variables not in the formula are not part of the model") {
    val result = solveForSatisfiability(x1)
    assert(result !== None)
    result.foreach(m => {
      assert(m(x1))
      assert(!m.isDefinedAt(x2))
      assert(!m.isDefinedAt(x3))
    })
  }

  test("Combination of basic boolean operators works as expected") {
    val f1 = (x1 || x2) && !x1
    val result = solveForSatisfiability(f1)
    assert(result !== None)
    result.foreach(model => {
      assert(!model(x1))
      assert(model(x2))
    })
  }

  test("solveForSatisfiability returns None on unsat example") {
    val f1 = (x1 || x2) && !x1
    val result = solveForSatisfiability(f1 && !x2)
    assert(result === None)
  }

  test("Formulas built with iff work as expected") {
    val f1 = (x1 iff x2) && !x1
    val r1 = solveForSatisfiability(f1 && x2)
    assert(r1 === None)
    val r2 = solveForSatisfiability(f1 && !x2)
    assert(r2 !== None)
    r2.foreach(model => {
      assert(!model(x1))
      assert(!model(x2))
    })
  }

  test("Formulas built with xor work as expected") {
    val f1 = (x1 xor x2) && !x1
    val r1 = solveForSatisfiability(f1 && !x2)
    assert(r1 === None)
    val r2 = solveForSatisfiability(f1 && x2)
    assert(r2 !== None)
    r2.foreach(model => {
      assert(!model(x1))
      assert(model(x2))
    })
  }


  test("Modeling simple circuit") {
    val p = propVar("p")
    val q = propVar("q")
    val np = propVar("p'")
    val nq = propVar("q'")
    val c1 = propVar("c1")
    val c2 = propVar("c2")
    val r = propVar("r")

    val f = (
      (np iff !p) &&
      (nq iff !q) &&
      (c1 iff (!p || q)) &&
      (c2 iff (p || !q)) &&
      (r iff (c1 && c2)) &&
      (!p iff r)
    )

    val r1 = solveForSatisfiability(f && p)
    assert(r1 !== None) 
    r1.foreach(model => {
      assert(model(p))
      assert(!model(q))
      assert(!model(r))
    })

    val r2 = solveForSatisfiability(f && q)
    assert(r2 === None)

  }

}
