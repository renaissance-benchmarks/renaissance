package cafesat.sat

// Invariant: different literal types are stored in different id intervals

// actualType is necessary because Literal can't be inherited, due to Set
// invariance (when using Set[Set[Literal]] as CNF)
class Literal(private val id: Int, private var offset: Int, val polInt: Int, val actualType: LiteralType) {
  require(id >= 0)

  def this(id: Int, polarity: Boolean, actualType: LiteralType = PropLiteral) = this(id, 0, if(polarity) 1 else 0, actualType)

  def this(id: Int, actualType: LiteralType) = this(id, 0, 0, actualType)

  def polarity = polInt == 1

  lazy val pos = new Literal(this.id, this.offset, 1, this.actualType) // TODO this is polluting

  //TODO: neg returns this ?
  def neg = this

  // getId must be extended when there are more LiteralType
  def getID = id + offset

  def setOffset(offset: Int): Unit = {
    this.offset = offset
  }

  override def toString: String = (if(!polarity) "-" else "") + "v" + getID

}

sealed trait LiteralType
case object TLiteral extends LiteralType
case object PropLiteral extends LiteralType

