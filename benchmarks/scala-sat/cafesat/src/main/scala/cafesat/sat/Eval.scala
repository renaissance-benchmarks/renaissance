package cafesat
package sat

/* Simple evaluator for cnf formulas */
object Eval {

  /* eval a cnf formula (set of clauses) with an assignment from variable
     to truth value.
   */
  def apply(clauses: Set[Set[Literal]], model: Array[Boolean]): Boolean = {
    clauses.forall(cl => cl.exists(lit => model(lit.getID) == lit.polarity))
  }

}
