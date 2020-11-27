package cafesat
package api

import asts.core.Trees.{Formula => CoreFormula, _}
import asts.fol.Trees.{True => CoreTrue, False => CoreFalse, _}
import asts.fol.Manip.{simplify => folSimplify, _}

/** Contains type definitions for formulas. 
  *
  * If you wish to instantiate a [[Formula]] or a [[PropVar]], you need
  * to use [[FormulaBuilder]] that will provide a generator function to
  * create [[PropVar]], and then build your formula from combinator 
  * methods in [[Formula]].
  *
  * Here is a simple example that shows how to build a formula:
  * {{{
  * import FormulaBuilder._
  * import Formulas._
  *
  * val a: PropVar = propVar("a")
  * val b: PropVar = propVar("b")
  * val f: Formula = a && (!a || b)
  * }}}
  *
  */
object Formulas {

  /*
   * Formulas provides only private constructors in order to hide the underlying
   * implementation of formulas to external project. The idea is that Formulas should
   * only be created via simple boolean operators provided in the api package.
   * Currently, I don't see a good use case for having access to the underlying representation,
   * such as the formula tree. My vision is that people want to use CafeSat as a solver,
   * and they should not need to manipulate the formula beyond building it.
   */

  /** Represents a propositional formula.
    *
    * The constructor is private, as a formula should 
    * always be created from helper functions in [[FormulaBuilder]].
    */
  class Formula private[api](
    private[api] val formula: CoreFormula
  ) {

    /** Returns the conjunction of `this` and `that`. */
    def &&(that: Formula): Formula = new Formula(And(this.formula, that.formula))

    /** Returns the disjunction of `this` and `that`. */
    def ||(that: Formula): Formula = new Formula(Or(this.formula, that.formula))

    /** Returns the negation of `this`. */
    def unary_! : Formula = new Formula(Not(this.formula))

    /** Returns a formula representing the equivalence of `this` and `that`. */
    def iff(that: Formula): Formula = new Formula(Or(
                                                   And(this.formula, that.formula), 
                                                   And(Not(this.formula), Not(that.formula))))

    /** Returns a formula representing the xor of `this` and `that`. */
    def xor(that: Formula): Formula = new Formula(Or(
                                                   And(this.formula, Not(that.formula)), 
                                                   And(Not(this.formula), that.formula)))

    /** Returns the number of nodes in the Formula
      *
      * A variable counts as one node, and any conjunction, disjunction,
      * and negation of a node counts as an additional node.
      */
    def size = asts.core.Manip.size(this.formula)

    override def equals(other: Any): Boolean = other match {
      case (that: Formula) => this.formula == that.formula
      case _ => false
    }

    override def hashCode: Int = this.formula.hashCode

    override def toString: String = asts.fol.PrettyPrinter(this.formula)
  }


  /** Represents a propositional variable.
    *
    * The constructor is private to the package, you can get an instance
    * of PropVar by using [[FormulaBuilder.propVar]].
    */
  class PropVar private[api](f: CoreFormula) extends Formula(f)

  /** Represents the always true formula. */
  object True extends Formula(CoreTrue())

  /** Represents the always false formula. */
  object False extends Formula(CoreFalse())

}
