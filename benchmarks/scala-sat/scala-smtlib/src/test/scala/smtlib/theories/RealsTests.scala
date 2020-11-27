package smtlib
package theories

import Reals._

import org.scalatest.funsuite.AnyFunSuite

class RealsTests extends AnyFunSuite {

  override def suiteName = "Reals theory test suite"

  test("Real sort") {
    RealSort() match {
      case RealSort() => assert(true)
      case _ => assert(false)
    }

    RealSort() match {
      case FixedSizeBitVectors.BitVectorSort(n) if n == 14 => assert(false)
      case FixedSizeBitVectors.BitVectorSort(n) if n == 32 => assert(false)
      case Ints.IntSort() => assert(false)
      case RealSort() => assert(true)
      case _ => assert(false)
    }
  }

  test("literals") {
    val l1 = NumeralLit(42)

    l1 match {
      case NumeralLit(n) => assert(n == 42)
      case _ => assert(false)
    }

    val l2 = DecimalLit(BigDecimal("13.41"))

    l2 match {
      case NumeralLit(n) => assert(false)
      case DecimalLit(d) => assert(d == BigDecimal("13.41"))
      case _ => assert(false)
    }
  }


  test("smtlib format") {
    import parser.Parser

    Parser.fromString("12").parseTerm match {
      case NumeralLit(n) => assert(n == 12)
      case _ => assert(false)
    }


    Parser.fromString("(- 13)").parseTerm match {
      case Neg(NumeralLit(n)) => assert(n == 13)
      case _ => assert(false)
    }
    Parser.fromString("(- 13 17)").parseTerm match {
      case Sub(
            NumeralLit(n1),
            NumeralLit(n2)
           ) => assert(n1 == 13 && n2 == 17)
      case _ => assert(false)
    }
    Parser.fromString("(+ 13 17)").parseTerm match {
      case Add(
            NumeralLit(n1),
            NumeralLit(n2)
           ) => assert(n1 == 13 && n2 == 17)
      case _ => assert(false)
    }
    Parser.fromString("(* 13 17)").parseTerm match {
      case Mul(
            NumeralLit(n1),
            NumeralLit(n2)
           ) => assert(n1 == 13 && n2 == 17)
      case _ => assert(false)
    }

  }
}
