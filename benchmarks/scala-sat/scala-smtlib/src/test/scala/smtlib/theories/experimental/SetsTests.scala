package smtlib
package theories
package experimental

import trees.Terms._

import Sets._
import Ints.{IntSort, NumeralLit}

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

class SetsTests extends AnyFunSuite with Matchers {

  override def suiteName = "Set theory test suite"

  test("String sort correctly constructed and extracted") {
    SetSort(IntSort()) match {
      case SetSort(IntSort()) => assert(true)
      case _ => assert(false)
    }

    SetSort(IntSort()) match {
      case FixedSizeBitVectors.BitVectorSort(n) if n == 14 => assert(false)
      case FixedSizeBitVectors.BitVectorSort(n) if n == 32 => assert(false)
      case Ints.IntSort() => assert(false)
      case Reals.RealSort() => assert(false)
      case SetSort(IntSort()) => assert(true)
      case _ => assert(false)
    }
  }

  test("EmptySet is correctly constructed and extracted") {
    EmptySet(IntSort()) match {
      case EmptySet(IntSort()) => assert(true)
      case _ => assert(false)
    }

    EmptySet(IntSort()) match {
      case EmptySet(Reals.RealSort()) => assert(false)
      case NumeralLit(_) => assert(false)
      case EmptySet(IntSort()) => assert(true)
      case _ => ???
    }
  }

  test("Singleton is correctly constructed and extracted") {
    Singleton(NumeralLit(42)) match {
      case Singleton(NumeralLit(n)) => assert(n === 42)
      case _ => assert(false)
    }

    Singleton(EmptySet(IntSort())) match {
      case EmptySet(IntSort()) => assert(false)
      case Singleton(NumeralLit(_)) => assert(false)
      case Singleton(EmptySet(IntSort())) => assert(true)
      case _ => assert(false)
    }
  }

  test("Union is correctly constructed and extracted") {
    Union(EmptySet(IntSort()), Singleton(NumeralLit(42))) match {
      case Union(EmptySet(IntSort()), Singleton(NumeralLit(n))) => assert(n === 42)
      case _ => assert(false)
    }
  }

}
