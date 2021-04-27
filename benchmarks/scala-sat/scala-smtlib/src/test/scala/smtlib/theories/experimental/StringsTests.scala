package smtlib
package theories
package experimental

import trees.Terms._

import Strings._
import Ints.NumeralLit

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

class StringsTests extends AnyFunSuite with Matchers {

  override def suiteName = "Strings theory test suite"

  test("String sort correctly constructed and extracted") {
    StringSort() match {
      case StringSort() => assert(true)
      case _ => assert(false)
    }

    StringSort() match {
      case FixedSizeBitVectors.BitVectorSort(n) if n == 14 => assert(false)
      case FixedSizeBitVectors.BitVectorSort(n) if n == 32 => assert(false)
      case Ints.IntSort() => assert(false)
      case Reals.RealSort() => assert(false)
      case StringSort() => assert(true)
      case _ => assert(false)
    }
  }

  test("literals are correctly constructed and extracted") {
    val l1 = StringLit("abc")

    l1 match {
      case StringLit(n) => assert(n === "abc")
      case _ => assert(false)
    }
    
    val l2 = StringLit("")

    l2 match {
      case StringLit(n) => assert(n === "")
      case _ => assert(false)
    }
    
    val l3 = StringLit("with space")

    l3 match {
      case StringLit(n) => assert(n === "with space")
      case _ => assert(false)
    }
  }

  test("Length is correctly constructed and extracted") {
    val l1 = Length(StringLit("abcd"))
    l1 match {
      case Length(StringLit("abcd")) => assert(true)
      case _ => assert(false)
    }


    val l2 = Length(StringLit("aaaa"))
    l2 match {
      case Length(StringLit("aaaa")) => assert(true)
      case _ => assert(false)
    }
  }

  test("Concat is correctly constructed and extracted") {
    val c1 = Concat(StringLit("ab"), StringLit("cd"))
    c1 match {
      case Concat(StringLit("ab"), StringLit("cd")) => assert(true)
      case _ => assert(false)
    }

    val c2 = Concat(StringLit("ab"), StringLit("cd"), StringLit("ef"))
    c2 match {
      case Concat(StringLit("ab"), StringLit("cd"), StringLit("ef")) => assert(true)
      case _ => assert(false)
    }

    val c3 = Concat(StringLit("ab"), StringLit("cd"), StringLit("ef"))
    c3 match {
      case Concat(StringLit("ab")) => assert(false)
      case Concat(StringLit("ab"), StringLit("cd")) => assert(false)
      case Concat(StringLit("ab"), StringLit("cd"), StringLit("ef")) => assert(true)
      case _ => assert(false)
    }

    val c4 = Concat(StringLit("ab"), StringLit("cd"), StringLit("ef"))
    c4 match {
      case Concat(ts@_*) => {
        assert(ts(0) === StringLit("ab"))
        assert(ts(1) === StringLit("cd"))
        assert(ts(2) === StringLit("ef"))
      }
      case _ => assert(false)
    }
   
  }

  test("At is correctly constructed and extracted") {
    val a = At(StringLit("xxx"), NumeralLit(2))
    a match {
      case At(StringLit("xxx"), NumeralLit(two)) => assert(two === 2)
      case _ => assert(false)
    }
  }

  test("Substring is correctly constructed and extracted") {
    val s = Substring(StringLit("abcdef"), NumeralLit(2), NumeralLit(5))
    s match {
      case Substring(StringLit("abcdef"), NumeralLit(two), NumeralLit(five)) => {
        assert(two === 2)
        assert(five === 5)
      }
      case _ => assert(false)
    }
  }


  test("smtlib string format") {
    import parser.Parser
    
    implicit class TestParse(s: String) {
      def shouldParse(f: PartialFunction[Term, Any]) = {
        val term = Parser.fromString(s).parseTerm
        if(f.isDefinedAt(term)) f(term) else {
          sys.error("Term " + s + " wrongly parsed as " + term)
        }
      }
      def shouldParseTo(p: Term) = {
        Parser.fromString(s).parseTerm should equal(p)
      }
    }
    
    
    "\"abc\"" shouldParseTo
    StringLit("abc")

    "(str.++ \"a\" \"bc\" )" shouldParseTo
    Concat(StringLit("a"), StringLit("bc"))

    "(str.++ \"a\" \"bc\" \"def\" )" shouldParseTo
    Concat(StringLit("a"), StringLit("bc"), StringLit("def"))
    
    "(str.len \"abcd\")" shouldParseTo
    Length(StringLit("abcd"))
    
    "(str.at \"abcd\" 1)" shouldParseTo
    At(StringLit("abcd"), NumeralLit(1))
    
    "(str.substr \"abcdef\" 2 5)" shouldParseTo
    Substring(StringLit("abcdef"), NumeralLit(2), NumeralLit(5))
  }
}
