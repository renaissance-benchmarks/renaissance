package smtlib
package trees

import org.scalatest.funsuite.AnyFunSuite

import Terms._
import Commands._
import TreesOps._

class TreesOpsTests extends AnyFunSuite {

  val s1 = Sort(Identifier(SSymbol("S1")))
  val s2 = Sort(Identifier(SSymbol("S2")))
  val s3 = Sort(Identifier(SSymbol("S3")), Seq(s1, s2))

  val v1 = QualifiedIdentifier(Identifier(SSymbol("v1")))
  val v2 = QualifiedIdentifier(Identifier(SSymbol("v2")))
  val v3 = QualifiedIdentifier(Identifier(SSymbol("v3")))

  val f1 = QualifiedIdentifier(Identifier(SSymbol("f1")))
  val f2 = QualifiedIdentifier(Identifier(SSymbol("f2")))
  val f3 = QualifiedIdentifier(Identifier(SSymbol("f3")))

  test("count function is 1 if exactly one variable") {
    assert(count(t => t == v1)(v1) === 1)
  }
  test("count function is 0 if variable has different name") {
    assert(count(t => t == v2)(v1) === 0)
  }
  test("count function finds and count variable just once") {
    assert(count(t => t == v1)(FunctionApplication(f1, Seq(v1))) === 1)
    assert(count(t => t == v1)(FunctionApplication(f1, Seq(v1, v2))) === 1)
    assert(count(t => t == v2)(FunctionApplication(f1, Seq(v1, v2))) === 1)
  }
  test("count function finds and count variable several times") {
    assert(count(t => t == v1)(FunctionApplication(f1, Seq(v1))) === 1)
    assert(count(t => t == v1)(FunctionApplication(f1, Seq(v1, v1))) === 2)
    assert(count(t => t == v1)(FunctionApplication(f1, Seq(v1, v2, v1))) === 2)
    assert(count(t => t == v1)(FunctionApplication(f1, Seq(FunctionApplication(f2, Seq(v1, v2)), v1, v2, v1))) === 3)
  }

  test("count function finds and count variable in commands") {
    assert(count(t => t == v1)(Assert(FunctionApplication(f1, Seq(v1)))) === 1)
    assert(count(t => t == v1)(Assert(FunctionApplication(f1, Seq(FunctionApplication(f2, Seq(v1, v2)), v1, v2, v1)))) === 3)
  }

  test("count function finds and count literals just once") {
    assert(count(t => t == SNumeral(42))(FunctionApplication(f1, Seq(SNumeral(42)))) === 1)
    assert(count(t => t == SNumeral(42))(FunctionApplication(f1, Seq(SNumeral(42), SNumeral(17)))) === 1)
    assert(count(t => t == SNumeral(42))(FunctionApplication(f1, Seq(SNumeral(0), SNumeral(42)))) === 1)
  }
  test("count function finds and count literals several times") {
    assert(count(t => t == SNumeral(42))(FunctionApplication(f1, Seq(SNumeral(42)))) === 1)
    assert(count(t => t == SNumeral(42))(FunctionApplication(f1, Seq(SNumeral(42), SNumeral(42)))) === 2)
    assert(count(t => t == SNumeral(42))(FunctionApplication(f1, Seq(SNumeral(42), SNumeral(17), SNumeral(42)))) === 2)
    assert(count(t => t == SNumeral(42))(FunctionApplication(f1, Seq(FunctionApplication(f2, Seq(SNumeral(42), v2)), SNumeral(42), v2, SNumeral(42)))) === 3)
  }

  test("exists function finds a variable that appears once") {
    assert(exists(t => t == v1)(FunctionApplication(f1, Seq(v1))) === true)
    assert(exists(t => t == v1)(FunctionApplication(f1, Seq(v1, v2))) === true)
    assert(exists(t => t == v2)(FunctionApplication(f1, Seq(v1, v2))) === true)
  }
  test("exists function does not find a variable that does not appears once") {
    assert(exists(t => t == v2)(FunctionApplication(f1, Seq(v1))) === false)
    assert(exists(t => t == v3)(FunctionApplication(f1, Seq(v1, v2))) === false)
    assert(exists(t => t == v3)(FunctionApplication(f1, Seq(v1, v2))) === false)
  }

}
