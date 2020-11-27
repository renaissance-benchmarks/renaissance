package smtlib
package trees

import org.scalatest.funsuite.AnyFunSuite

import Terms._
import TermsOps._

class TermsOpsTests extends AnyFunSuite {

  val s1 = Sort(Identifier(SSymbol("S1")))
  val s2 = Sort(Identifier(SSymbol("S2")))
  val s3 = Sort(Identifier(SSymbol("S3")), Seq(s1, s2))

  def sortId(s: Sort): Option[Sort] = Some(s)

  def s12s2(s: Sort): Option[Sort] = if(s == s1) Some(s2) else None

  test("postMap with empty function do not change simple sort") {
    assert(postMap((s: Sort) => None)(s1) === s1)
    assert(postMap((s: Sort) => None)(s2) === s2)
  }

  test("postMap with empty function do not change composed sort") {
    assert(postMap((s: Sort) => None)(s3) === s3)
  }

  test("postMap with id maps simple sorts to themselves") {
    assert(postMap(sortId)(s1) === s1)
    assert(postMap(sortId)(s2) === s2)
  }

  test("postMap with id maps composed sorts to themselves") {
    assert(postMap(sortId)(s3) === s3)
  }

  test("postMap with simple mapping works on simple term") {
    assert(postMap(s12s2)(s1) === s2)
    assert(postMap(s12s2)(s2) === s2)
  }

  test("postMap with simple mapping works on a leaf of a composed term") {
    assert(postMap(s12s2)(s3) === Sort(Identifier(SSymbol("S3")), Seq(s2, s2)))
  }


  test("preMap with empty function do not change simple sort") {
    assert(preMap((s: Sort) => None)(s1) === s1)
    assert(preMap((s: Sort) => None)(s2) === s2)
  }

  test("preMap with empty function do not change composed sort") {
    assert(preMap((s: Sort) => None)(s3) === s3)
  }

  test("preMap with id maps simple sorts to themselves") {
    assert(preMap(sortId)(s1) === s1)
    assert(preMap(sortId)(s2) === s2)
  }

  test("preMap with id maps composed sorts to themselves") {
    assert(preMap(sortId)(s3) === s3)
  }

  test("preMap with simple mapping works on simple term") {
    assert(preMap(s12s2)(s1) === s2)
    assert(preMap(s12s2)(s2) === s2)
  }

  test("preMap with simple mapping works on a leaf of a composed term") {
    assert(preMap(s12s2)(s3) === Sort(Identifier(SSymbol("S3")), Seq(s2, s2)))
  }
}
