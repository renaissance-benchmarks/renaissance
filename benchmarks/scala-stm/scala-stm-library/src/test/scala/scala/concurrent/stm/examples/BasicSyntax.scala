/* scala-stm - (c) 2009-2010, Stanford University, PPL */

package scala.concurrent.stm
package examples

object BasicSyntax {
  case class Point(x: Int, y: Int)
  val origin = Point(0, 0)
  
  val top = Ref(origin)
  val bottom = Ref(origin)
  val left = Ref(origin)
  val right = Ref(origin)

  def updateExtremes(p: Point) {
    atomic { implicit txn =>
      if (p.x < left().x)
        left() = p
      if (p.x > right().x)
        right() = p
      if (p.y < top().y)
        top() = p
      if (p.y > bottom().y)
        bottom() = p
    }
  }

  def alternatives {
    val z = atomic { implicit txn =>
      if (!(left().x < -100))
        retry
      "left"
    } orAtomic { implicit txn =>
      if (!(right().x > +100))
        retry
      "right"
    } orAtomic { implicit txn =>
      if (!(top().y < -100))
        retry
      "top"
    } orAtomic { implicit txn =>
      if (!(bottom().y > +100))
        retry
      "bottom"
    }
    println("first out was " + z)
  }
  
}
