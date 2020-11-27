package smtlib
package common

import org.scalatest.funsuite.AnyFunSuite

class BinaryTests extends AnyFunSuite {

  test("toIntBits works with one bit") {
    assert(Binary(List(true)).toIntBits === 1)
    assert(Binary(List(false)).toIntBits === 0)
  }

  test("toIntBits works with a few bits") {
    assert(Binary(List(true, true)).toIntBits === 3)
    assert(Binary(List(true, false, true)).toIntBits === 5)
  }

  test("toIntBits correctly ignores leading zeros") {
    assert(Binary(List(false, true)).toIntBits === 1)
    assert(Binary(List(false, true, false, true)).toIntBits === 5)
  }

  test("toIntBits works with exactly 32 digits") {
    val allOnes: List[Boolean] = List[Boolean]().padTo(32, true)
    assert(Binary(allOnes).toIntBits === -1)
  }

  test("toIntBits ignores digits after 32") {
    val allOnes: List[Boolean] = List[Boolean]().padTo(32, true)
    assert(Binary(true :: allOnes).toIntBits === -1)
    assert(Binary(false :: allOnes).toIntBits === -1)
    assert(Binary(true :: false :: allOnes).toIntBits === -1)
    assert(Binary(false :: true :: allOnes).toIntBits === -1)

    val allZeros: List[Boolean] = List[Boolean]().padTo(32, false)
    assert(Binary(true :: allZeros).toIntBits === 0)
    assert(Binary(false :: allZeros).toIntBits === 0)
    assert(Binary(true :: false :: allZeros).toIntBits === 0)
    assert(Binary(false :: true :: allZeros).toIntBits === 0)
  }

  test("toLongBits works with one bit") {
    assert(Binary(List(true)).toLongBits === 1)
    assert(Binary(List(false)).toLongBits === 0)
  }

  test("toLongBits works with a few bits") {
    assert(Binary(List(true, true)).toLongBits === 3)
    assert(Binary(List(true, false, true)).toLongBits === 5)
  }

  test("toLongBits correctly ignores leading zeros") {
    assert(Binary(List(false, true)).toLongBits === 1)
    assert(Binary(List(false, true, false, true)).toLongBits === 5)
  }

  test("toInt works with one bit") {
    assert(Binary(List(true)).toInt === -1)
    assert(Binary(List(false)).toInt === 0)
  }

  test("toInt works with a few bits") {
    assert(Binary(List(true, true)).toInt === -1)
    assert(Binary(List(false, true, true)).toInt === 3)
    assert(Binary(List(false, true, false, true)).toInt === 5)
    assert(Binary(List(true, false, true)).toInt === -3)
  }

}
