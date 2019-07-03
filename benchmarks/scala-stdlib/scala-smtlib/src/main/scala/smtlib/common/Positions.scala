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


trait Positioned {

  private[this] var _pos: Option[Position] = None

  def setPos(pos: Position): this.type = {
    _pos = Some(pos)
    this
  }
    
  def setPos(that: Positioned): this.type = {
    _pos = Some(that.getPos)
    this
  }

  def getPos: Position = {
    _pos.get
  }
}
