package smtlib
package theories

import Core._

import org.scalatest.FunSuite

class CoreTests extends FunSuite {

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
