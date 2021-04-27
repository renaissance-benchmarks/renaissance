package smtlib
package common


/** Hexadecimal number value
  *
  * This provides a type safe way to manipulate hexadecimal number.
  * The main constructor is private, but the companion object provides
  * a number of way to produce an Hexadecimal representation, from a
  * string or from any integer type.
  *
  * An hexadecimal number value really depends on the context in which
  * it is considered. It can always be interpreted as an unsigned, infinite
  * precision integer, or as a negative number in two-complement. A value
  * like 'F' could either be 16 or -1, depending if it is interpreted as an
  * unsigned value on an integral type of more than 4 bits, or if it is sign
  * extended in the corresponding integral representation. You should consider
  * the Hexadecimal as a concise syntax to represent a sequence of bytes, with
  * convenient methods to convert to and from integers, and not as an actual
  * number.
  */
class Hexadecimal private(
  /** The string representation, using upper cases */
  val repr: String
) {
  //should be normalized to upper cases
  require(repr.forall(c =>
    (c >= '0' && c <= '9') || (c >= 'A' && c <= 'F')
  ))

  /** extract the Int represented by this hexadecimal
    * 
    * Returns the Int value represented by this hexadecimal number.
    * Assumes the hexadecimal represents 32 bits, by padding 0 in
    * front if necessary, and by ignoring extra digits.
    *
    * It returns the Int encoded with the exact 32 bits, meaning
    * it could return negative number.
    */
  def toInt: Int = {
    val padding = repr.reverse.drop(16)
    require(padding.forall(c => c == '0'))

    repr.foldLeft(0)((acc, c) => {
      acc*16 + c.asDigit//asDigit works for 'A', 'F', ...
    })
  }

  def toBinary: List[Boolean] = {
    repr.flatMap{
      case '0' => List(false, false, false, false)
      case '1' => List(false, false, false, true )
      case '2' => List(false, false, true , false)
      case '3' => List(false, false, true , true )
      case '4' => List(false, true , false, false)
      case '5' => List(false, true , false, true )
      case '6' => List(false, true , true , false)
      case '7' => List(false, true , true , true )
      case '8' => List(true , false, false, false)
      case '9' => List(true , false, false, true )
      case 'A' => List(true , false, true , false)
      case 'B' => List(true , false, true , true )
      case 'C' => List(true , true , false, false)
      case 'D' => List(true , true , false, true )
      case 'E' => List(true , true , true , false)
      case 'F' => List(true , true , true , true )
    }.toList
  }

  override def toString: String = "#x" + repr

  override def equals(that: Any): Boolean = (that != null) && (that match {
    case (h: Hexadecimal) => repr == h.repr
    case _ => false
  })

  override def hashCode: Int = repr.hashCode

  //TODO: take subpart of hexa (trunc from 32 bits to 8 bits for example)

}

object Hexadecimal {

  def fromString(str: String): Option[Hexadecimal] = {
    var error = false
    val repr = str.map(c => {
      if(isDigit(c)) 
        c.toUpper
      else {
        error = true
        c
      }
    })
    if(error) None else Some(new Hexadecimal(repr))
  }

  /** return a 32-bits hexadecimal integer */
  def fromInt(n: Int): Hexadecimal = {
    if(n < 0) {
      val res = "00000000".toArray
      for(i <- 0 until 8) {
        val digit = (n >> (32 - 4*(i+1))) & 15
        res(i) = toDigit(digit)
      }
      fromString(res.mkString).get
    } else {

      var i = 0
      var rest = n
      var repr = ""

      while(i < 8) {
        val end = rest & 15
        rest = rest >> 4
        repr = s"${toDigit(end)}$repr"
        i += 1
      }

      fromString(repr).get
    }
  }

  def fromByte(b: Byte): Hexadecimal = fromBigInt(BigInt(b), 2)

  def fromShort(s: Short): Hexadecimal = fromBigInt(BigInt(s), 4)

  def fromLong(l: Long): Hexadecimal = fromBigInt(BigInt(l), 16)


  /** convert a BigInt to an Hexadecimal
    *
    * The resulting hexadecimal will always be of size specified
    * by digits. The conversion always truncates the theoretical
    * representation, which could have the effect of changing
    * a positive integer into a negative value.
    *
    * Negative numbers are converted by taking the theoretical
    * two complement representation, with an infinite number of
    * 1s in front, and then we simply truncate for the correct length.
    * It has the effect that it could change a negative number into
    * a positive number in the corresponding length.
    */
  def fromBigInt(bi: BigInt, digits: Int): Hexadecimal = {
    val isPositive = bi >= 0
    val absolute = bi.abs
    val absoluteRepr: String = absolute.toString(16)

    if(isPositive) {
      fromString(absoluteRepr.reverse.take(digits).padTo(digits, '0').reverse).get
    } else {

      val bytes: Array[Byte] = bi.toByteArray
      val fullHexa: String = bytes.map(b => byteToHexString(b)).mkString

      fromString(fullHexa.reverse.take(digits).padTo(digits, 'F').reverse).get
    }

  }

  def toDigit(n: Int): Char = {
    require(n >= 0 && n < 16)
    if(n >= 0 && n < 10) (n + '0').toChar else ('A' + (n - 10)).toChar
  }

  /** convert a digit byte to corresponding char
    *
    * Only works for bytes between 0 and 16
    */
  def toDigit(n: Byte): Char = {
    require(n >= 0 && n < 16)
    if(n >= 0 && n < 10) (n + '0').toChar else ('A' + (n - 10)).toChar
  }


  def isDigit(c: Char): Boolean =
    c.isDigit || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F')

  /* generate a two-digit (0-f) hex string for the given byte. */
  private def byteToHexString(b: Byte): String = {
    val h = Integer.toHexString(b)
    if (b >= 0) {
      val missing = 2 - h.length
      ("0" * missing) + h
    } else {
      val extra = h.length - 2
      h.drop(extra)
    }
  }

}
