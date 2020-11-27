package smtlib.common

case class Position(line: Int, col: Int) extends Ordered[Position] {

  def compare(that: Position) = {
    val ld = this.line - that.line
    if (ld == 0) {
      this.col - that.col
    } else {
      ld
    }
  }

  override def toString: String = s"($line, $col)"

}


/** Adds a position attribute to objects
  *
  * The position is optional, first because of the nature of trait
  * it is cumbersome to force a position at instantiation time. But
  * mainly because we don't want to always force a Term or Command
  * to have a position. Typically, if the Command is generated from a
  * program, its position should be None. All terms parsed from some
  * input should have a position relative to the input.
  *
  * Position is always a single line+col, which should generally be
  * interpreted as the position of the first character corresponding
  * to the token/object. We might want to consider a solution for describing
  * starting+ending position
  */
trait Positioned {

  private[this] var _pos: Option[Position] = None

  def setPos(pos: Position): this.type = {
    _pos = Some(pos)
    this
  }
    
  def setPos(that: Positioned): this.type = {
    _pos = that.optPos
    this
  }

  def getPos: Position = {
    _pos.get
  }

  def optPos: Option[Position] = _pos

  def hasPos: Boolean = _pos.nonEmpty
}
