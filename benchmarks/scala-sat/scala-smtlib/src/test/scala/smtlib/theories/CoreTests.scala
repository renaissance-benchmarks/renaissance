package smtlib
package theories

import trees.Terms._
import Core._

import org.scalatest.funsuite.AnyFunSuite

class CoreTests extends AnyFunSuite {

  override def suiteName = "Core Theory test suite"

  test("Bool sort") {
    val s = BoolSort()

    s match {
      case BoolSort() => assert(true)
      case _ => assert(false)
    }
  }

  test("literals") {
    val t = True()
    val f = False()

    t match {
      case False() => assert(false)
      case True() => assert(true)
      case _ => assert(false)
    }

    f match {
      case True() => assert(false)
      case False() => assert(true)
      case _ => assert(false)
    }
  }

  test("basic boolean op") {
    val t = True()
    val f = False()

    val not = Not(t)
    not match {
      case Not(x) => 
        assert(x == t)
      case _ => assert(false)
    }

    val ortf = Or(t, f)
    val ortt = Or(t, t)
    val orff = Or(f, f)

    ortf match {
      case And(x, y) => assert(false)
      case Or(x, y) =>
        assert(x == t)
        assert(y == f)
      case _ => assert(false)
    }

    val and = And(t, f)
    and match {
      case Or(x, y) => assert(false)
      case And(x, y) =>
        assert(x == t)
        assert(y == f)
      case _ => assert(false)
    }

    val xor = Xor(t, f)
    xor match {
      case Or(x, y) => assert(false)
      case And(x, y) => assert(false)
      case Xor(x, y) => 
        assert(x == t)
        assert(y == f)
      case _ => assert(false)
    }

    val implies = Implies(t, f)
    implies match {
      case Or(x, y) => assert(false)
      case And(x, y) => assert(false)
      case Implies(x, y) => 
        assert(x == t)
        assert(y == f)
      case _ => assert(false)
    }

  }

  //test("And varargs constructor properly builds formulas") {
  //  val f1 = QualifiedIdentifier(SimpleIdentifier(SSymbol("f1")))
  //  val f2 = QualifiedIdentifier(SimpleIdentifier(SSymbol("f2")))
  //  val f3 = QualifiedIdentifier(SimpleIdentifier(SSymbol("f3")))

  //  val a0 = And()
  //  assert(a0 === True())

  //  val a1 = And(f1)
  //  assert(a1 === f1)

  //  val a2 = And(f1, f2, f3)
  //  assert(a2 === And(f1, And(f2, f3)) || a2 === And(And(f1, f2), f3))
  //}

  //test("Or varargs constructor properly builds formulas") {
  //  val f1 = QualifiedIdentifier(SimpleIdentifier(SSymbol("f1")))
  //  val f2 = QualifiedIdentifier(SimpleIdentifier(SSymbol("f2")))
  //  val f3 = QualifiedIdentifier(SimpleIdentifier(SSymbol("f3")))

  //  val o0 = Or()
  //  assert(o0 === False())

  //  val o1 = Or(f1)
  //  assert(o1 === f1)

  //  val o2 = Or(f1, f2, f3)
  //  assert(o2 === Or(f1, Or(f2, f3)) || o2 === Or(Or(f1, f2), f3))
  //}

  test("smtlib format") {
    import parser.Parser

    Parser.fromString("true").parseTerm match {
      case True() => assert(true)
      case _ => assert(false)
    }

    Parser.fromString("false").parseTerm match {
      case False() => assert(true)
      case _ => assert(false)
    }

    Parser.fromString("(not true)").parseTerm match {
      case False() => assert(false)
      case True() => assert(false)
      case Not(True()) => assert(true)
      case _ => assert(false)
    }

    Parser.fromString("(or true false)").parseTerm match {
      case False() => assert(false)
      case True() => assert(false)
      case Not(True()) => assert(false)
      case And(True(), False()) => assert(false)
      case Or(True(), True()) => assert(false)
      case Or(True(), False()) => assert(true)
      case _ => assert(false)
    }

    Parser.fromString("(and true false)").parseTerm match {
      case False() => assert(false)
      case True() => assert(false)
      case Not(True()) => assert(false)
      case Or(True(), False()) => assert(false)
      case And(True(), True()) => assert(false)
      case And(True(), False()) => assert(true)
      case _ => assert(false)
    }

    Parser.fromString("(=> true false)").parseTerm match {
      case False() => assert(false)
      case True() => assert(false)
      case Not(True()) => assert(false)
      case Or(True(), False()) => assert(false)
      case Implies(True(), True()) => assert(false)
      case Implies(True(), False()) => assert(true)
      case _ => assert(false)
    }

    Parser.fromString("(xor true false)").parseTerm match {
      case False() => assert(false)
      case True() => assert(false)
      case Not(True()) => assert(false)
      case Or(True(), False()) => assert(false)
      case Xor(True(), True()) => assert(false)
      case Xor(True(), False()) => assert(true)
      case _ => assert(false)
    }
  }

}
