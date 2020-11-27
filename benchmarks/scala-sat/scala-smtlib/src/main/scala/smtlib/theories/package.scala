package smtlib

/** Provides constructors and extractors to build theory specific trees
  *
  * Theory trees are not concrete abstract syntax trees, but simply helpers
  * to properly construct the underlying low level {{smtlib.parser.Terms AST}}.
  * 
  * This design choice is made to reflect how the SMT-LIB format is described,
  * and also seems to work well as most operations on trees only need to be
  * defined for the core ASTs. Many theories operations such as "+", "-", "div"
  * are really a special case of the general 
  * {{smtlib.parser.Terms.FunctionApplication FunctionApplication}}.
  *  
  * Each theory is defined in its own object named after the theory, e.g.
  * {theories.Ints}, which contains objects with `apply` and `unapply` (usually
  * factored out in some abstract {{theory.Operations}} traits) to build and
  * extract correct expressions in the theory.
  */
package object theories {

}
