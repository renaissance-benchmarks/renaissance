package smtlib
package theories

import trees.Terms._
import ArraysEx._
import Ints.{IntSort, NumeralLit}

import org.scalatest.funsuite.AnyFunSuite

class ArraysExTests extends AnyFunSuite {

  override def suiteName = "ArraysEx Theory test suite"

  test("Array sort is correctly constructed and extracted") {
    ArraySort(IntSort(), IntSort()) match {
      case ArraySort(IntSort(), IntSort()) => assert(true)
      case _ => assert(false)
    }
  }

  test("Select is correctly constructed and extracted") {
    val a = QualifiedIdentifier(SimpleIdentifier(SSymbol("a")))
    Select(a, NumeralLit(0)) match {
      case Select(x, NumeralLit(i)) =>
        assert(x === a)
        assert(i === 0)
      case _ => assert(false)
    }
  }

  test("Store is correctly constructed and extracted") {
    val a = QualifiedIdentifier(SimpleIdentifier(SSymbol("a")))
    Store(a, NumeralLit(0), NumeralLit(12)) match {
      case Store(x, NumeralLit(i), NumeralLit(v)) =>
        assert(x === a)
        assert(i === 0)
        assert(v === 12)
      case _ => assert(false)
    }
  }

}
