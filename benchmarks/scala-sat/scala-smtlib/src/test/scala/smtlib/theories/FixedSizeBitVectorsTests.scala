package smtlib
package theories

import FixedSizeBitVectors._
import parser.Parser

import org.scalatest.funsuite.AnyFunSuite

class FixedSizeBitVectorsTests extends AnyFunSuite {

  override def suiteName = "Bit Vector theory test suite"

  test("BitVector sort") {
    BitVectorSort(32) match {
      case BitVectorSort(n) if n == 14 => assert(false)
      case BitVectorSort(n) if n == 32 => assert(true)
      case _ => assert(false)
    }

    BitVectorSort(12) match {
      case BitVectorSort(n) if n == 14 => assert(false)
      case BitVectorSort(n) if n == 32 => assert(false)
      case BitVectorSort(n) if n == 12 => assert(true)
      case _ => assert(false)
    }
  }

  test("literals") {
    val l1 = BitVectorLit(List(true, true, false))

    l1 match {
      case BitVectorLit(List(true, false, true)) => assert(false)
      case BitVectorLit(List(true, true, false, false)) => assert(false)
      case BitVectorLit(List(true, true, false)) => assert(true)
      case _ => assert(false)
    }

  }

  test("smtlib bv constant notation") {
    Parser.fromString("(_ bv13 32)").parseTerm match {
      case BitVectorConstant(x, n) if x == 12 && n == 32 => assert(false)
      case BitVectorConstant(x, n) if x == 13 && n == 31 => assert(false)
      case BitVectorConstant(x, n) if x == 13 && n == 32 => assert(true)
      case _ => assert(false)
    }
    Parser.fromString("(_ bv11 17)").parseTerm match {
      case BitVectorConstant(x, n) if x == 12 && n == 17 => assert(false)
      case BitVectorConstant(x, n) if x == 11 && n == 32 => assert(false)
      case BitVectorConstant(x, n) if x == 11 && n == 17 => assert(true)
      case _ => assert(false)
    }
    Parser.fromString("(_ bv10242 77)").parseTerm match {
      case BitVectorConstant(x, n) if x == 10242 && n == 77 => assert(true)
      case _ => assert(false)
    }
    Parser.fromString("(_ bv1234567891234 200)").parseTerm match {
      case BitVectorConstant(x, n) if x == BigInt("1234567891234") && n == 200 => assert(true)
      case _ => assert(false)
    }

    val cst = BitVectorConstant(13, 32)
    cst match {
      case BitVectorConstant(x, n) if x == 13 && n == 32 => assert(true)
      case _ => assert(false)
    }
  }

  test("smtlib bv constant with int overflow") {
    val cst = BitVectorConstant(BigInt("2147483648"), 32)
    cst match {
      case BitVectorConstant(x, n) if x.toInt == -2147483648 && n == 32 => assert(true)
      case _ => assert(false)
    }
  }

  test("smtlib is correctly parsed with bv literals") {

    Parser.fromString("#b101").parseTerm match {
      case BitVectorLit(List(true, false, true)) => assert(true)
      case _ => assert(false)
    }
    Parser.fromString("#xf0").parseTerm match {
      case BitVectorLit(List(true, true, true, true, false, false, false, false)) => assert(true)
      case _ => assert(false)
    }

  }

  test("smtlib is correctly parsed with bv manipulation operations") {

    Parser.fromString("(concat #b101 #b01)").parseTerm match {
      case Concat(
            BitVectorLit(List(true, false, true)),
            BitVectorLit(List(false, true))
           ) => assert(true)
      case _ => assert(false)
    }
    Parser.fromString("((_ extract 1 2) #b101)").parseTerm match {
      case Extract(x, y, BitVectorLit(List(true, false, true))) if x == 1 && y == 2 => assert(true)
      case _ => assert(false)
    }
    Parser.fromString("((_ repeat 5) #b101)").parseTerm match {
      case Repeat(n, BitVectorLit(List(true, false, true))) if n == 5 => assert(true)
      case _ => assert(false)
    }
    Parser.fromString("((_ zero_extend 3) #b101)").parseTerm match {
      case ZeroExtend(n, BitVectorLit(List(true, false, true))) if n == 3 => assert(true)
      case _ => assert(false)
    }
    Parser.fromString("((_ sign_extend 3) #b101)").parseTerm match {
      case SignExtend(n, BitVectorLit(List(true, false, true))) if n == 3 => assert(true)
      case _ => assert(false)
    }
    Parser.fromString("((_ rotate_left 3) #b101)").parseTerm match {
      case RotateLeft(n, BitVectorLit(List(true, false, true))) if n == 3 => assert(true)
      case _ => assert(false)
    }
    Parser.fromString("((_ rotate_right 3) #b101)").parseTerm match {
      case RotateRight(n, BitVectorLit(List(true, false, true))) if n == 3 => assert(true)
      case _ => assert(false)
    }
  }

  test("smtlib is correctly parsed with bv logical operations") {
    Parser.fromString("(bvnot #b101)").parseTerm match {
      case Not(
            BitVectorLit(List(true, false, true))
          ) => assert(true)
      case _ => assert(false)
    }
    Parser.fromString("(bvand #b101 #b011)").parseTerm match {
      case And(
            BitVectorLit(List(true, false, true)),
            BitVectorLit(List(false, true, true))
           ) => assert(true)
      case _ => assert(false)
    }
    Parser.fromString("(bvor #b101 #b011)").parseTerm match {
      case Or(
            BitVectorLit(List(true, false, true)),
            BitVectorLit(List(false, true, true))
           ) => assert(true)
      case _ => assert(false)
    }
    Parser.fromString("(bvnand #b101 #b011)").parseTerm match {
      case NAnd(
            BitVectorLit(List(true, false, true)),
            BitVectorLit(List(false, true, true))
           ) => assert(true)
      case _ => assert(false)
    }
    Parser.fromString("(bvnor #b101 #b011)").parseTerm match {
      case NOr(
            BitVectorLit(List(true, false, true)),
            BitVectorLit(List(false, true, true))
           ) => assert(true)
      case _ => assert(false)
    }
    Parser.fromString("(bvxor #b101 #b011)").parseTerm match {
      case XOr(
            BitVectorLit(List(true, false, true)),
            BitVectorLit(List(false, true, true))
           ) => assert(true)
      case _ => assert(false)
    }
    Parser.fromString("(bvxnor #b101 #b011)").parseTerm match {
      case XNOr(
            BitVectorLit(List(true, false, true)),
            BitVectorLit(List(false, true, true))
           ) => assert(true)
      case _ => assert(false)
    }
    Parser.fromString("(bvcomp #b101 #b011)").parseTerm match {
      case Comp(
            BitVectorLit(List(true, false, true)),
            BitVectorLit(List(false, true, true))
           ) => assert(true)
      case _ => assert(false)
    }
  }

  test("smtlib is correctly parsed with bv arithmetic operations") {
    Parser.fromString("(bvneg #b101)").parseTerm match {
      case Neg(
            BitVectorLit(List(true, false, true))
          ) => assert(true)
      case _ => assert(false)
    }
    Parser.fromString("(bvadd #b101 #b011)").parseTerm match {
      case Add(
            BitVectorLit(List(true, false, true)),
            BitVectorLit(List(false, true, true))
           ) => assert(true)
      case _ => assert(false)
    }
    Parser.fromString("(bvsub #b101 #b011)").parseTerm match {
      case Sub(
            BitVectorLit(List(true, false, true)),
            BitVectorLit(List(false, true, true))
           ) => assert(true)
      case _ => assert(false)
    }
    Parser.fromString("(bvmul #b101 #b011)").parseTerm match {
      case Mul(
            BitVectorLit(List(true, false, true)),
            BitVectorLit(List(false, true, true))
           ) => assert(true)
      case _ => assert(false)
    }
    Parser.fromString("(bvudiv #b101 #b011)").parseTerm match {
      case UDiv(
            BitVectorLit(List(true, false, true)),
            BitVectorLit(List(false, true, true))
           ) => assert(true)
      case _ => assert(false)
    }
    Parser.fromString("(bvsdiv #b101 #b011)").parseTerm match {
      case SDiv(
            BitVectorLit(List(true, false, true)),
            BitVectorLit(List(false, true, true))
           ) => assert(true)
      case _ => assert(false)
    }
    Parser.fromString("(bvurem #b101 #b011)").parseTerm match {
      case URem(
            BitVectorLit(List(true, false, true)),
            BitVectorLit(List(false, true, true))
           ) => assert(true)
      case _ => assert(false)
    }
    Parser.fromString("(bvsrem #b101 #b011)").parseTerm match {
      case SRem(
            BitVectorLit(List(true, false, true)),
            BitVectorLit(List(false, true, true))
           ) => assert(true)
      case _ => assert(false)
    }
    Parser.fromString("(bvsmod #b101 #b011)").parseTerm match {
      case SMod(
            BitVectorLit(List(true, false, true)),
            BitVectorLit(List(false, true, true))
           ) => assert(true)
      case _ => assert(false)
    }
  }

  test("smtlib is correctly parsed with bv shifting operations") {
    Parser.fromString("(bvshl #b101 #b011)").parseTerm match {
      case ShiftLeft(
            BitVectorLit(List(true, false, true)),
            BitVectorLit(List(false, true, true))
           ) => assert(true)
      case _ => assert(false)
    }
    Parser.fromString("(bvlshr #b101 #b011)").parseTerm match {
      case LShiftRight(
            BitVectorLit(List(true, false, true)),
            BitVectorLit(List(false, true, true))
           ) => assert(true)
      case _ => assert(false)
    }
    Parser.fromString("(bvashr #b101 #b011)").parseTerm match {
      case AShiftRight(
            BitVectorLit(List(true, false, true)),
            BitVectorLit(List(false, true, true))
           ) => assert(true)
      case _ => assert(false)
    }

  }


  test("smtlib is correctly parsed with bv arithmetic comparisons operations") {
    Parser.fromString("(bvult #b101 #b011)").parseTerm match {
      case ULessThan(
            BitVectorLit(List(true, false, true)),
            BitVectorLit(List(false, true, true))
           ) => assert(true)
      case _ => assert(false)
    }
    Parser.fromString("(bvslt #b101 #b011)").parseTerm match {
      case SLessThan(
            BitVectorLit(List(true, false, true)),
            BitVectorLit(List(false, true, true))
           ) => assert(true)
      case _ => assert(false)
    }
    Parser.fromString("(bvule #b101 #b011)").parseTerm match {
      case ULessEquals(
            BitVectorLit(List(true, false, true)),
            BitVectorLit(List(false, true, true))
           ) => assert(true)
      case _ => assert(false)
    }
    Parser.fromString("(bvsle #b101 #b011)").parseTerm match {
      case SLessEquals(
            BitVectorLit(List(true, false, true)),
            BitVectorLit(List(false, true, true))
           ) => assert(true)
      case _ => assert(false)
    }
    Parser.fromString("(bvugt #b101 #b011)").parseTerm match {
      case UGreaterThan(
            BitVectorLit(List(true, false, true)),
            BitVectorLit(List(false, true, true))
           ) => assert(true)
      case _ => assert(false)
    }
    Parser.fromString("(bvsgt #b101 #b011)").parseTerm match {
      case SGreaterThan(
            BitVectorLit(List(true, false, true)),
            BitVectorLit(List(false, true, true))
           ) => assert(true)
      case _ => assert(false)
    }
    Parser.fromString("(bvuge #b101 #b011)").parseTerm match {
      case UGreaterEquals(
            BitVectorLit(List(true, false, true)),
            BitVectorLit(List(false, true, true))
           ) => assert(true)
      case _ => assert(false)
    }
    Parser.fromString("(bvsge #b101 #b011)").parseTerm match {
      case SGreaterEquals(
            BitVectorLit(List(true, false, true)),
            BitVectorLit(List(false, true, true))
           ) => assert(true)
      case _ => assert(false)
    }
  }
}
