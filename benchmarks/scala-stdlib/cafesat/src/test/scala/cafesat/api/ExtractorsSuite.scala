package cafesat.api

import FormulaBuilder._
import Extractors._

import org.scalatest.FunSuite


class ExtractorsSuite extends FunSuite {

  private val x1 = propVar()
  private val x2 = propVar()
  private val x3 = propVar()

  test("Disjunction of two variables is extracted as an Or") {
    val f = x1 || x2
    f match {
      case Or(y1, y2) => {
        assert(x1 === y1)
        assert(x2 === y2)
      }
      case _ => assert(false)
    }
  }

  test("Nested disjunctions extract correctly") {
    val f = (x1 || x2) || x3
    f match {
      case Or(Or(y1, y2), y3) => {
        assert(x1 === y1)
        assert(x2 === y2)
        assert(x3 === y3)
      }
      case _ => assert(false)
    }
  }

  test("Conjunction of two variables is extracted as an And") {
    val f = x1 && x2
    f match {
      case And(y1, y2) => {
        assert(x1 === y1)
        assert(x2 === y2)
      }
      case _ => assert(false)
    }
  }

  test("Nested conjunctions extract correctly") {
    val f = (x1 && x2) && x3
    f match {
      case And(And(y1, y2), y3) => {
        assert(x1 === y1)
        assert(x2 === y2)
        assert(x3 === y3)
      }
      case _ => assert(false)
    }
  }

  test("Conjunctions not extracted as an Or") {
    val f = (x1 && x2) && x3
    f match {
      case Or(_, _) => assert(false)
      case _ => assert(true)
    }
  }

  test("Negation of a variable extracts correctly") {
    val f = !x1
    f match {
      case Not(y1) => {
        assert(x1 === y1)
      }
      case _ => assert(false)
    }
  }

  test("Nested negations extract correctly") {
    val f1 = !x1
    val f2 = !f1
    f2 match {
      case Not(Not(y1)) => assert(x1 === y1)
      case _ => assert(true)
    }
  }
}
