package smtlib
package theories

import Ints._

import org.scalatest.funsuite.AnyFunSuite

class IntsTests extends AnyFunSuite {

  override def suiteName = "Ints theory test suite"

  test("IntSort is correctly constructed and extracted") {
    IntSort() match {
      case IntSort() => assert(true)
      case _ => assert(false)
    }

    IntSort() match {
      case FixedSizeBitVectors.BitVectorSort(_) => assert(false)
      case IntSort() => assert(true)
      case _ => assert(false)
    }
  }

  test("NumeralLit is correctly constructed and extracted") {
    val l1 = NumeralLit(42)

    l1 match {
      case NumeralLit(n) => assert(n === 42)
      case _ => assert(false)
    }

  }

  test("Divisible is correctly constructed and extracted") {
    Divisible(BigInt(3), NumeralLit(9)) match {
      case Divisible(d, NumeralLit(n)) => 
        assert(n === 9)
        assert(d === 3)
      case _ => assert(false)
    }
  }

  test("Neg is correctly constructed and extracted") {
    Neg(NumeralLit(23)) match {
      case Neg(NumeralLit(n)) => assert(n === 23)
      case _ => assert(false)
    }
  }

  test("Add is correctly constructed and extracted") {
    Add(NumeralLit(23), NumeralLit(112)) match {
      case Add(NumeralLit(n1), NumeralLit(n2)) => 
        assert(n1 === 23)
        assert(n2 === 112)
      case _ => assert(false)
    }
  }

  test("Sub is correctly constructed and extracted") {
    Sub(NumeralLit(23), NumeralLit(112)) match {
      case Sub(NumeralLit(n1), NumeralLit(n2)) => 
        assert(n1 === 23)
        assert(n2 === 112)
      case _ => assert(false)
    }
  }

  test("Mul is correctly constructed and extracted") {
    Mul(NumeralLit(23), NumeralLit(112)) match {
      case Mul(NumeralLit(n1), NumeralLit(n2)) => 
        assert(n1 === 23)
        assert(n2 === 112)
      case _ => assert(false)
    }
  }

  test("Div is correctly constructed and extracted") {
    Div(NumeralLit(10), NumeralLit(2)) match {
      case Div(NumeralLit(n1), NumeralLit(n2)) => 
        assert(n1 === 10)
        assert(n2 === 2)
      case _ => assert(false)
    }
  }

  test("Mod is correctly constructed and extracted") {
    Mod(NumeralLit(10), NumeralLit(2)) match {
      case Mod(NumeralLit(n1), NumeralLit(n2)) => 
        assert(n1 === 10)
        assert(n2 === 2)
      case _ => assert(false)
    }
  }
  test("Abs is correctly constructed and extracted") {
    Abs(NumeralLit(23)) match {
      case Abs(NumeralLit(n)) => assert(n === 23)
      case _ => assert(false)
    }
  }


  test("LessThan is correctly constructed and extracted") {
    LessThan(NumeralLit(10), NumeralLit(2)) match {
      case LessThan(NumeralLit(n1), NumeralLit(n2)) => 
        assert(n1 === 10)
        assert(n2 === 2)
      case _ => assert(false)
    }
  }

  test("LessEquals is correctly constructed and extracted") {
    LessEquals(NumeralLit(10), NumeralLit(2)) match {
      case LessEquals(NumeralLit(n1), NumeralLit(n2)) => 
        assert(n1 === 10)
        assert(n2 === 2)
      case _ => assert(false)
    }
  }

  test("GreaterThan is correctly constructed and extracted") {
    GreaterThan(NumeralLit(10), NumeralLit(2)) match {
      case GreaterThan(NumeralLit(n1), NumeralLit(n2)) => 
        assert(n1 === 10)
        assert(n2 === 2)
      case _ => assert(false)
    }
  }

  test("GreaterEquals is correctly constructed and extracted") {
    GreaterEquals(NumeralLit(10), NumeralLit(2)) match {
      case GreaterEquals(NumeralLit(n1), NumeralLit(n2)) => 
        assert(n1 === 10)
        assert(n2 === 2)
      case _ => assert(false)
    }
  }

  test("Extractors correctly extract parsed strings") {
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
