package cafesat
package sat

import Solver.Results._
import Solver.Clause

import org.scalatest.funsuite.AnyFunSuite

class IncrementalSuite extends AnyFunSuite {

  private implicit val emptyContext = Context(util.SilentLogger)

  private val a = new Literal(0, true)
  private val na = new Literal(0, false)
  private val b = new Literal(1, true)
  private val nb = new Literal(1, false)

  test("Incremental run sat/unsat with assumption") {
    val s = new Solver(2)

    val clauses = List(Set(na, b))
    clauses.foreach(s.addClause(_))
    val result1 = s.solve()
    assert(result1.isInstanceOf[Satisfiable])

    s.addClause(Set(na, nb))
    val result2 = s.solve(Array(a))
    assert(result2 === Unsatisfiable)
  }

  test("empty solve call") {
    val s = new Solver(0)
    val result = s.solve()
    // vacuously true (sat) should be okay
    assert(result.isInstanceOf[Satisfiable])
  }

}
