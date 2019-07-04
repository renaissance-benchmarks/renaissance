package smtlib
package theories

import Ints._

import org.scalatest.FunSuite

class IntsTests extends FunSuite {

  override def suiteName = "Ints theory test suite"

  test("Int sort") {
    IntSort() match {
      case IntSort() => assert(true)
      case _ => assert(false)
    }

    IntSort() match {
      case FixedSizeBitVectors.BitVectorSort(14) => assert(false)
      case IntSort() => assert(true)
      case _ => assert(false)
    }
  }

  test("literals") {
    val l1 = NumeralLit(42)

    l1 match {
      case NumeralLit(n) => assert(n == 42)
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
