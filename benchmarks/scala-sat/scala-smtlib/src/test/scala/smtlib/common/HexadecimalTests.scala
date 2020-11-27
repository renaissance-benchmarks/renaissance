package smtlib
package common

import org.scalatest.funsuite.AnyFunSuite

class HexadecimalTests extends AnyFunSuite {

  test("Build hexadecimal with one digit string") {
    val zero = Hexadecimal.fromString("0")
    assert(zero !== None)
    zero.foreach(zero => assert(zero.repr === "0"))
    
    val one = Hexadecimal.fromString("1")
    assert(one !== None)
    one.foreach(one => assert(one.repr === "1"))
    
    val ten = Hexadecimal.fromString("A")
    assert(ten !== None)
    ten.foreach(ten => assert(ten.repr === "A"))
  }

  test("Build hexadecimal with strings of multiple digits") {
    val hexa1 = Hexadecimal.fromString("12AB")
    assert(hexa1 !== None)
    hexa1.foreach(hexa1 => assert(hexa1.repr === "12AB"))

    val hexa2 = Hexadecimal.fromString("00F2")
    assert(hexa2 !== None)
    hexa2.foreach(hexa2 => assert(hexa2.repr === "00F2"))
  }

  test("Build hexadecimal with lower caps is represented as upper caps") {
    val hexa1 = Hexadecimal.fromString("a")
    assert(hexa1 !== None)
    hexa1.foreach(hexa1 => assert(hexa1.repr === "A"))

    val hexa2 = Hexadecimal.fromString("00fa")
    assert(hexa2 !== None)
    hexa2.foreach(hexa2 => assert(hexa2.repr === "00FA"))
  }

  test("Build hexadecimal from an invalid string returns None") {
    val hexa1 = Hexadecimal.fromString("g")
    assert(hexa1 === None)

    val hexa2 = Hexadecimal.fromString("0g")
    assert(hexa2 === None)

    val hexa3 = Hexadecimal.fromString("g001")
    assert(hexa3 === None)
  }


  test("toInt returns correct value for small positive numbers") {
    assert(Hexadecimal.fromString("0").get.toInt === 0)
    assert(Hexadecimal.fromString("1").get.toInt === 1)
    assert(Hexadecimal.fromString("a").get.toInt === 10)
    assert(Hexadecimal.fromString("f").get.toInt === 15)
    assert(Hexadecimal.fromString("10").get.toInt === 16)
    assert(Hexadecimal.fromString("1a").get.toInt === 26)
    assert(Hexadecimal.fromString("001a").get.toInt === 26)
    assert(Hexadecimal.fromString("3a").get.toInt === 58)
  }

  test("toInt returns correct value for negative numbers") {
    assert(Hexadecimal.fromString("FFFFFFFF").get.toInt === -1)
    assert(Hexadecimal.fromString("FFFFFFFE").get.toInt === -2)
    assert(Hexadecimal.fromString("80000000").get.toInt === -2147483648)
  }

  test("toInt ignores leading bits above 32") {
    assert(Hexadecimal.fromString("0000003a").get.toInt === 58)
    assert(Hexadecimal.fromString("000000003a").get.toInt === 58)
    assert(Hexadecimal.fromString("FF0000003a").get.toInt === 58)
    assert(Hexadecimal.fromString("FFFFFFFFFF").get.toInt === -1)
    assert(Hexadecimal.fromString("00FFFFFFFF").get.toInt === -1)
  }

  test("fromInt converts positive ints to hexadecimal") {
    assert(Hexadecimal.fromInt(0).repr === "00000000")
    assert(Hexadecimal.fromInt(1).repr === "00000001")
    assert(Hexadecimal.fromInt(15).repr === "0000000F")
    assert(Hexadecimal.fromInt(30).repr === "0000001E")
    assert(Hexadecimal.fromInt(2147483647).repr === "7FFFFFFF")
  }

  test("fromInt converts negative ints to hexadecimal") {
    assert(Hexadecimal.fromInt(-1).repr === "FFFFFFFF")
    assert(Hexadecimal.fromInt(-2).repr === "FFFFFFFE")
    assert(Hexadecimal.fromInt(-81).repr === "FFFFFFAF")
    assert(Hexadecimal.fromInt(-2147483648).repr === "80000000")
  }

  test("fromByte converts positive bytes to hexadecimal") {
    assert(Hexadecimal.fromByte(0).repr === "00")
    assert(Hexadecimal.fromByte(1).repr === "01")
    assert(Hexadecimal.fromByte(15).repr === "0F")
    assert(Hexadecimal.fromByte(30).repr === "1E")
    assert(Hexadecimal.fromByte(127).repr === "7F")
  }

  test("fromByte converts negative int to hexadecimal") {
    assert(Hexadecimal.fromByte(-1).repr === "FF")
    assert(Hexadecimal.fromByte(-2).repr === "FE")
    assert(Hexadecimal.fromByte(-81).repr === "AF")
    assert(Hexadecimal.fromByte(-128).repr === "80")
  }

  test("fromShort converts positive bytes to hexadecimal") {
    assert(Hexadecimal.fromShort(0).repr === "0000")
    assert(Hexadecimal.fromShort(1).repr === "0001")
    assert(Hexadecimal.fromShort(15).repr === "000F")
    assert(Hexadecimal.fromShort(30).repr === "001E")
    assert(Hexadecimal.fromShort(32767).repr === "7FFF")
  }

  test("fromShort converts negative int to hexadecimal") {
    assert(Hexadecimal.fromShort(-1).repr === "FFFF")
    assert(Hexadecimal.fromShort(-2).repr === "FFFE")
    assert(Hexadecimal.fromShort(-81).repr === "FFAF")
    assert(Hexadecimal.fromShort(-32768).repr === "8000")
  }

  test("fromBigInt converts positive ints to hexadecimal") {
    assert(Hexadecimal.fromBigInt(0, 1).repr === "0")
    assert(Hexadecimal.fromBigInt(1, 1).repr === "1")
    assert(Hexadecimal.fromBigInt(15,1).repr === "F")
    assert(Hexadecimal.fromBigInt(0, 2).repr === "00")
    assert(Hexadecimal.fromBigInt(1, 2).repr === "01")
    assert(Hexadecimal.fromBigInt(15,2).repr === "0F")
    assert(Hexadecimal.fromBigInt(30,2).repr === "1E")
  }

  test("fromBigInt ignores ints leading digits if not enough digits") {
    assert(Hexadecimal.fromBigInt(16, 1).repr === "0")
    assert(Hexadecimal.fromBigInt(17, 1).repr === "1")
    assert(Hexadecimal.fromBigInt(31, 1).repr === "F")
  }

  test("fromBigInt converts negative ints to hexadecimal") {
    assert(Hexadecimal.fromBigInt(-1, 1).repr === "F")
    assert(Hexadecimal.fromBigInt(-2, 1).repr === "E")
    assert(Hexadecimal.fromBigInt(-1, 2).repr === "FF")
    assert(Hexadecimal.fromBigInt(-2, 2).repr === "FE")
    assert(Hexadecimal.fromBigInt(-81,2).repr === "AF")
    assert(Hexadecimal.fromBigInt(-1, 4).repr === "FFFF")

    assert(Hexadecimal.fromBigInt(-128, 2).repr === "80")
    assert(Hexadecimal.fromBigInt(-128, 4).repr === "FF80")
    assert(Hexadecimal.fromBigInt(-127, 4).repr === "FF81")
    assert(Hexadecimal.fromBigInt(-129, 4).repr === "FF7F")
  }

  test("fromBigInt ignores leading '1's for negative ints") {
    assert(Hexadecimal.fromBigInt(-128, 1).repr === "0")
    assert(Hexadecimal.fromBigInt(-127, 1).repr === "1")
    assert(Hexadecimal.fromBigInt(-129, 1).repr === "F")
    assert(Hexadecimal.fromBigInt(-32768, 1).repr === "0")

    assert(Hexadecimal.fromBigInt(-16, 1).repr === "0")
    assert(Hexadecimal.fromBigInt(-81, 1).repr === "F")
    assert(Hexadecimal.fromBigInt(-18, 1).repr === "E")
    assert(Hexadecimal.fromBigInt(-19, 1).repr === "D")
    assert(Hexadecimal.fromBigInt(-28, 1).repr === "4")
  }

}
