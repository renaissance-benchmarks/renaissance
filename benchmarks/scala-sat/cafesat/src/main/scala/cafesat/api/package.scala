package cafesat

/** Provides a simple abstraction on top of CafeSat functionalities.
  *
  * This is the expected entry point to use CafeSat as a library. 
  * It provides a simple and high-level abstraction over
  * formulas with an opaque type [[Formulas.Formula]], along 
  * with a simple language to build formulas and query their satisfiability.
  *
  * [[Formulas]] contains the main definitions for the core types used to
  * represent formulas.
  *
  * [[FormulaBuilder]] provides the main building blocks to build formulas.
  * You typically start a formula with a [[FormulaBuilder.propVar]] to obtain
  * a propositional variable and then you can use boolean operators to build
  * a more complex formula out of it.
  *
  * [[cafesat.api.Solver$ Solver]] provides functions to query a solver over formulas.
  *
  * Here is a short example where CafeSat is used to check the satisfiability of
  * a simple formula:
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
  *     println("a is: " + model(a))
  *     println("b is: " + model(b))
  *   }
  * }
  * }}}
  */
package object api {

}
