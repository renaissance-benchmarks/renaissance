package cafesat.api

import FormulaBuilder._
import Extractors._

import org.scalatest.funsuite.AnyFunSuite


class FormulasSuite extends AnyFunSuite {

  private val x1 = propVar()
  private val x2 = propVar()
  private val x3 = propVar()

  test("size of a variable should be 1") {
    assert(x1.size === 1)
    assert(x2.size === 1)
  }

  test("size of a disjunction of 2 variables should be 3") {
    assert((x1 || x2).size === 3)
  }

  test("size of a conjunction of 2 variables should be 3") {
    assert((x1 && x2).size === 3)
  }

  test("size of a nested conjunction and disjunction of 3 variables should be 5") {
    assert((x1 && x2 || x3).size === 5)
  }
}
