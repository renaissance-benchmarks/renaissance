package cafesat
package dpllt

import scala.reflect._

object BooleanTheory extends TheoryComponent {

  val literalClassTag: ClassTag[Literal] = classTag[PropositionalLiteral]

  type Literal = PropositionalLiteral
  case class PropositionalLiteral(id: Int, polInt: Int) extends AbstractLiteral {

    require(polInt == 1 | polInt == 0)
    def this(id: Int, pol: Boolean) = this(id, if(pol) 1 else 0)

    def neg = new PropositionalLiteral(id, 1-polInt)
    def pos = new PropositionalLiteral(id, 1)

    override def toString: String = (if(polarity) "" else "-") + "b_" + id
  }

  type Solver = PropositionalSolver
  /*
   * Assume that no duplicate literal is setTrue
   * Basically this is not a very correct implementation of the interface, but should allows
   * for efficient sat solving
   */
  class PropositionalSolver extends AbstractSolver {
    final override def backtrack(n: Int): Unit = {}

    final override def setTrue(l: Literal): Either[Set[Literal], Set[Literal]] = Left(Set())

    final override def isTrue(l: Literal) = true

    final override def explanation(l: Literal): Set[Literal] = Set()

    final override def check() = None
  }

  override def makeSolver(ls: Set[Set[Literal]]) = new PropositionalSolver

}
