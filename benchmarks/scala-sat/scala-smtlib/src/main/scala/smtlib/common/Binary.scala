package smtlib
package common

import scala.language.implicitConversions

class Binary private(val digits: List[Boolean]) {

  /*
   * TODO: a dimension/size concept
   */

  //take the 32 least significant bits
  def toIntBits: Int = {
    ((toLongBits << 32) >>> 32).toInt
  }

  def toLongBits: Long = {
    val allReversedBits: List[Boolean] = digits.take(64).reverse.padTo(64, false)
    allReversedBits.foldRight(0L)((bit, bits) => ((bits<<1) | (if(bit) 1 else 0)))
  }

  //transform to a 32 bits integer, respecting 2 complements
  def toInt: Int = {
    val allReversedBits: List[Boolean] = digits.take(32).reverse.padTo(32, digits.head)
    allReversedBits.foldRight(0)((bit, bits) => ((bits<<1) | (if(bit) 1 else 0)))
  }


  /*
   * TODO: define how the size is affected
   */
  def &(that: Binary): Binary = Binary(this.digits.zip(that.digits).map(p => p._1 && p._2))
  def |(that: Binary): Binary = {
    val (padThis, padThat) = 
      if(this.digits.size < that.digits.size)
        (this.digits.padTo(that.digits.size, false), that.digits)
      else
        (this.digits, that.digits.padTo(this.digits.size, false))
    Binary(padThis.zip(padThat).map(p => p._1 || p._2))
  }

  def ^(that: Binary): Binary = ???
  def >>(that: Binary): Binary = ???
  def >>>(that: Binary): Binary = ???
  def <<(that: Binary): Binary = ???
  
  def unary_~ : Binary = ???

}

object Binary {

  def apply(digits: List[Boolean]) = new Binary(digits)

  def apply(hexa: Hexadecimal) = new Binary(hexa.toBinary)

  implicit def int2binary(bitVector: Int): Binary = ???

}
