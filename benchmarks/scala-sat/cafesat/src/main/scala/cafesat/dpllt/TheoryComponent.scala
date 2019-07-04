package cafesat
package dpllt

import scala.reflect.ClassTag

trait TheoryComponent {

  implicit val literalClassTag: ClassTag[Literal]

  type Literal <: AbstractLiteral
  abstract class AbstractLiteral {
    val id: Int 
    val polInt: Int

    def polarity: Boolean = polInt == 1

    //returns the positive literal (always true)
    def pos: Literal
    //returns the negation of the literal
    def neg: Literal

    override def toString: String = (if(!polarity) "-" else "") + "l_" + id
    override def equals(o: Any): Boolean = o != null && (o match {
      case (lit: Literal) => id == lit.id && polInt == lit.polInt
      case _ => false
    })
  }


  type Solver <: AbstractSolver

  abstract class AbstractSolver {

    /*
     * Set the literal to true in the partial model.
     * return Left with a set of consequences (without completeness guarantees) if no conflict is detected
     * or Right with a conflict reason if a conflict is detected.
     * The check for consistency is not necessarly complete and an inconsistent partial model
     * could be maintained.
     */
    def setTrue(l: Literal): Either[Set[Literal], Set[Literal]]

    def isTrue(l: Literal): Boolean

    /*
     * Full check of the current consistency of the partial model.
     * If the state is inconsistent, it returns Some subset of the model that is unsatisfiable
     */
    def check(): Option[Set[Literal]]

    /*
     * Explain why a literal l was a consequence of a setTrue(l').
     * The explanation only returns valid explanations in the state where the literal l
     * was derived.
     */
    def explanation(l: Literal): Set[Literal]

    /*
     * Backtrack last n setTrue
     */
    def backtrack(n: Int): Unit
  }
  def makeSolver(ls: Set[Set[Literal]]): Solver

}
