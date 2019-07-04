package cafesat
package api

import Formulas.{Formula, PropVar}

import asts.fol.Trees._
import asts.fol.Manip._

import sat.{Solver => USolver} //U for Underlying
import sat.Solver.Results._
import sat.Solver.Clause
import sat.ConjunctiveNormalForm
import sat.Literal

import util._

trait Solver {

  type Var
  type Lit

  def newVar(): Var

  def mkLit(v: Var, pol: Boolean): Lit

  def addClause(lits: Vector[Lit]): Unit

  def solve(assumptions: Vector[Lit]): Boolean

  def model: Map[Var, Boolean]

}


/** Contains helper functions to query CafeSat solvers on formulas.
  *
  * Here is a simple example to get you started, we build a very simple formula
  * and then send it as a parameter to [[Solver.solveForSatisfiability solveForSatisfiability]] 
  * that returns an option of a [[Solver.Model Model]]:
  * {{{
  * import FormulaBuilder._
  * import Formulas._
  *
  * val a: PropVar = propVar("a")
  * val b: PropVar = propVar("b")
  * val f: Formula = a && (!a || b)
  * Solver.solveForSatisfiability(f) match {
  *   case None => {
  *     println("There is no solution")
  *   }
  *   case Some(model) => {
  *     val valueA: Boolean = model(a)
  *     val valueB: Boolean = model(b)
  *     println("a is: " valueA)
  *     println("b is: " valueB)
  *   }
  * }
  * }}}
  *
  */
object Solver {

  //should provide a way to configure in the API
  private implicit val defaultContext = Context(DefaultStdErrLogger)

  /** The type returned on a satisfiable instance.  */
  type Model = Map[PropVar, Boolean]

  /** Checks the satisfiability of a formula.
    *
    * @param formula the formula to check for satisfiability
    * @return `Some(model)` if the formula is satisfiable, and `None` if unsatisfiable
    */
  def solveForSatisfiability(formula: Formula): Option[Model] = {
    val f = formula.formula
    val simpleF = simplify(f)
    simpleF match {
      case True() => Some(Map()) //TODO: provide random values
      case False() => None
      case _ => {
        val (clauses, nbVars, mapping) = ConjunctiveNormalForm(simplify(f))
        val s = new USolver(nbVars)
        clauses.foreach(s.addClause(_))
        val solveRes = s.solve()
        solveRes match {
          case Satisfiable(model) =>
            Some(mapping.map(p => (new PropVar(p._1), model(p._2))))
          case Unsatisfiable => None
          case Unknown =>
            sys.error("shouldn't be unknown")
        }
      }
    }
  }

}
