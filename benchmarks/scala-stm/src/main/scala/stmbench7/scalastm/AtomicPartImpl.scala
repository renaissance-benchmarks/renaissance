/* scala-stm - (c) 2009-2011, Stanford University, PPL */

package stmbench7.scalastm

import scala.concurrent.stm.atomic
import scala.concurrent.stm.Ref
import scala.concurrent.stm.TSet

import stmbench7.core.AtomicPart
import stmbench7.core.CompositePart
import stmbench7.core.Connection
import stmbench7.impl.core.ConnectionImpl

class AtomicPartImpl(id0: Int, typ0: String, bd0: Int, x0: Int, y0: Int)
  extends DesignObjImpl(id0, typ0, bd0)
  with AtomicPart {

  private val x = Ref(x0)
  private val y = Ref(y0)
  private val partOf = Ref(null: CompositePart).single
  private val from = TSet.empty[Connection].single // this is the equivalent of SmallSetImpl
  private val to = TSet.empty[Connection].single

  override def connectTo(dest: AtomicPart, typ: String, length: Int): Unit = {
    val c = new ConnectionImpl(this, dest, typ, length)
    to += c
    dest.addConnectionFromOtherPart(c.getReversed)
  }

  override def addConnectionFromOtherPart(c: Connection): Unit = { from += c }
  override def setCompositePart(po: CompositePart): Unit = { partOf() = po }
  override def getNumToConnections: Int = to.size
  override def getToConnections = new ImmutableSetImpl[Connection](to)
  override def getFromConnections = new ImmutableSetImpl[Connection](from)
  override def getPartOf: CompositePart = partOf()

  override def swapXY(): Unit = {
    atomic { implicit t =>
      y() = x.swap(y())
    }
  }
  override def getX: Int = x.single()
  override def getY: Int = y.single()

  override def clearPointers(): Unit = {
    atomic { implicit t =>
      x() = 0
      y() = 0
      to.clear()
      from.clear()
      partOf() = null
    }
  }

  // Comparable[AtomicPart]
  override def compareTo(rhs: AtomicPart): Int =
    getId - rhs.getId // subtraction is faithful to reference impl
}
