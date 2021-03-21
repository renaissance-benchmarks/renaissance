package io.reactors
package events



import scala.collection._
import org.scalatest._
import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers



class IVarSpec extends AnyFunSuite with Matchers {

  test("be assigned") {
    val iv = new IVar[Int]
    iv := 5
    assert(iv() == 5)
    assert(iv.isAssigned)
  }

  test("be unreacted") {
    val iv = new IVar[Int]
    iv.unreact()
    assert(iv.isCompleted)
    assert(iv.isFailed)
  }

  test("throw") {
    val iv = new IVar[Int]
    iv.unreact()
    intercept[NoSuchElementException] {
      iv()
    }
  }

  test("be created empty") {
    val a = IVar.empty
    assert(a.isCompleted)
    assert(a.isFailed)
  }

}

