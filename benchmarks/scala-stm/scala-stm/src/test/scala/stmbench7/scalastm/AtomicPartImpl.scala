/* scala-stm - (c) 2009-2011, Stanford University, PPL */

package stmbench7.scalastm

import scala.concurrent.stm._
import stmbench7.core._
import stmbench7.impl.core.ConnectionImpl

class AtomicPartImpl(id0: Int, typ0: String, bd0: Int, x0: Int, y0: Int) extends DesignObjImpl(id0, typ0, bd0) with AtomicPart {
  val x = Ref(x0)
  val y = Ref(y0)
  val partOf = Ref(null : CompositePart).single
  val from = TSet.empty[Connection].single // this is the equivant of SmallSetImpl
  val to = TSet.empty[Connection].single

  def connectTo(dest: AtomicPart, typ: String, length: Int) {
    val c = new ConnectionImpl(this, dest, typ, length)
    to += c
    dest.addConnectionFromOtherPart(c.getReversed)
  }
  def addConnectionFromOtherPart(c: Connection) { from += c }
  def setCompositePart(po: CompositePart) { partOf() = po }
  def getNumToConnections = to.size
  def getToConnections = new ImmutableSetImpl[Connection](to)
  def getFromConnections = new ImmutableSetImpl[Connection](from)
  def getPartOf = partOf()
  def swapXY() {
    atomic { implicit t =>
      y() = x.swap(y())
    }
  }
  def getX = x.single()
  def getY = y.single()
  def clearPointers() {
    atomic { implicit t =>
      x() = 0
      y() = 0
      to.clear()
      from.clear()
      partOf() = null
    }
  }

  // Comparable[AtomicPart]
  def compareTo(rhs: AtomicPart) = getId - rhs.getId // subtraction is faithful to reference impl
}
