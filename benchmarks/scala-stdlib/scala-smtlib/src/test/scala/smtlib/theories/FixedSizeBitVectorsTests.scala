package smtlib
package theories

import FixedSizeBitVectors._

import org.scalatest.FunSuite

class FixedSizeBitVectorsTests extends FunSuite {

  override def suiteName = "Bit Vector theory test suite"

  test("BitVector sort") {
    BitVectorSort(32) match {
      case BitVectorSort(14) => assert(false)
      case BitVectorSort(32) => assert(true)
      case _ => assert(false)
    }

    BitVectorSort(12) match {
      case BitVectorSort(14) => assert(false)
      case BitVectorSort(32) => assert(false)
      case BitVectorSort(12) => assert(true)
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


  test("smtlib format") {
    import parser.Parser

    Parser.fromString("#b101").parseTerm match {
      case BitVectorLit(List(true, false, true)) => assert(true)
      case _ => assert(false)
    }
    Parser.fromString("#xf0").parseTerm match {
      case BitVectorLit(List(true, true, true, true, false, false, false, false)) => assert(true)
      case _ => assert(false)
    }

    Parser.fromString("(concat #b101 #b01)").parseTerm match {
      case Concat(
            BitVectorLit(List(true, false, true)),
            BitVectorLit(List(false, true))
           ) => assert(true)
      case _ => assert(false)
    }
    Parser.fromString("((_ extract 1 2) #b101)").parseTerm match {
      case Extract(1, 2, BitVectorLit(List(true, false, true))) => assert(true)
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

    Parser.fromString("(bvadd #b101 #b011)").parseTerm match {
      case Add(
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

  }
}
