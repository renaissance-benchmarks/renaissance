package org.renaissance.scala.sat

import cafesat.api.FormulaBuilder.and
import cafesat.api.FormulaBuilder.or
import cafesat.api.FormulaBuilder.propVar
import cafesat.api.Solver.solveForSatisfiability
import org.renaissance.Benchmark
import org.renaissance.Benchmark._
import org.renaissance.BenchmarkContext
import org.renaissance.BenchmarkResult
import org.renaissance.BenchmarkResult.ValidationException
import org.renaissance.BenchmarkResult.Validators
import org.renaissance.License

object Solver {

  /**
   * Solver takes a sudoku problem as a matrix of optional integers
   * and fills in the missing values to form a correct Sudoku grid.
   */
  def solve(sudoku: Array[Array[Option[Int]]]): Option[Array[Array[Int]]] = {

    /**
     * Each slot on the Sudoku board has 9 associated variables (V0..V8),
     * each variable Vi denoting whether the digit Vi was chosen for the
     * respective slot.
     */
    require(sudoku.length == 9)
    require(sudoku.forall(row => row.length == 9))

    val vars = sudoku.map(row => row.map(_ => Array.fill(9)(propVar())))

    /**
     * There should be at least one digit chosen for each sudoku slot.
     */
    val onePerEntry = vars.flatMap(row => row.map(vs => or(vs.toIndexedSeq: _*)))

    /**
     * There must be at most one any digit in each 3x3 table.
     * Here, `k` is the variable (digit), `i` and `j` are the coordinates of the 3x3 tables,
     * `r1` and `r2` are row pairs within the 3x3 table, and `c1` and `c2` are pairs of
     * columns within the 3x3 table.
     */
    val uniqueInGrid1 =
      for (
        k <- 0 to 8; i <- 0 to 2; j <- 0 to 2; r <- 0 to 2;
        c1 <- 0 to 1; c2 <- c1 + 1 to 2
      )
        yield !vars(3 * i + r)(3 * j + c1)(k) || !vars(3 * i + r)(3 * j + c2)(k)

    val uniqueInGrid2 =
      for (
        k <- 0 to 8; i <- 0 to 2; j <- 0 to 2; r1 <- 0 to 2;
        c1 <- 0 to 2; c2 <- 0 to 2; r2 <- r1 + 1 to 2
      )
        yield !vars(3 * i + r1)(3 * j + c1)(k) || !vars(3 * i + r2)(3 * j + c2)(k)

    /**
     * In the respective column, there should be at most one unique digit.
     */
    val uniqueInColumns =
      for (c <- 0 to 8; k <- 0 to 8; r1 <- 0 to 7; r2 <- r1 + 1 to 8)
        yield !vars(r1)(c)(k) || !vars(r2)(c)(k)

    /**
     * In the respective row, there should be at most one unique digit.
     */
    val uniqueInRows =
      for (r <- 0 to 8; k <- 0 to 8; c1 <- 0 to 7; c2 <- c1 + 1 to 8)
        yield !vars(r)(c1)(k) || !vars(r)(c2)(k)

    /**
     * Force entry with a possible number.
     */
    val forcedEntries =
      for (r <- 0 to 8; c <- 0 to 8 if sudoku(r)(c).isDefined)
        yield or(vars(r)(c)(sudoku(r)(c).get - 1))

    /**
     * All constraints for a sudoku problem.
     */
    val allConstraints = onePerEntry ++ uniqueInColumns ++ uniqueInRows ++
      uniqueInGrid1 ++ uniqueInGrid2 ++ forcedEntries

    /**
     * The whole grid should Satisfy all constraints.
     */
    solveForSatisfiability(and(allConstraints.toIndexedSeq: _*))
      .map(model => vars.map(row => row.map(vs => vs.indexWhere(v => model(v)) + 1)))
  }

}

@Name("scala-doku")
@Group("scala")
@Group("scala-sat")
@Summary("Solves Sudoku Puzzles using Scala collections.")
@Licenses(Array(License.MIT))
@Repetitions(20)
@Configuration(name = "test")
@Configuration(name = "jmh")
final class ScalaDoku extends Benchmark {

  /*
   * An arbitrary solved sudoku puzzle. The puzzle is copied and some entries
   * are changed to have an unsolved version for the algorithm to solve it again.
   */
  private val SOLVED_PUZZLE = Array(
    Array(6, 7, 9, 2, 8, 5, 3, 1, 4),
    Array(1, 4, 8, 9, 6, 3, 5, 2, 7),
    Array(2, 3, 5, 1, 7, 4, 8, 6, 9),
    Array(5, 6, 4, 3, 1, 9, 2, 7, 8),
    Array(8, 1, 3, 5, 2, 7, 4, 9, 6),
    Array(9, 2, 7, 8, 4, 6, 1, 5, 3),
    Array(3, 8, 6, 7, 5, 1, 9, 4, 2),
    Array(7, 5, 2, 4, 9, 8, 6, 3, 1),
    Array(4, 9, 1, 6, 3, 2, 7, 8, 5)
  )

  private var puzzleWithAFewHoles: Array[Array[Option[Int]]] = _

  private var puzzleWithOneHole: Array[Array[Option[Int]]] = _

  private def preparePuzzleWithAFewHoles() = {
    val result = SOLVED_PUZZLE.map(row => row.map(i => Some(i): Option[Int]))
    result(0)(0) = None
    result(4)(8) = None
    result(7)(7) = None
    result
  }

  private def preparePuzzleWithOneHole() = {
    val result = SOLVED_PUZZLE.map(row => row.map(i => Some(i): Option[Int]))
    result(2)(7) = None
    result
  }

  override def setUpBeforeAll(c: BenchmarkContext): Unit = {
    puzzleWithAFewHoles = preparePuzzleWithAFewHoles()
    puzzleWithOneHole = preparePuzzleWithOneHole()
  }

  override def run(c: BenchmarkContext): BenchmarkResult = {
    Validators.compound(
      new DokuResult(Solver.solve(puzzleWithAFewHoles), SOLVED_PUZZLE),
      new DokuResult(Solver.solve(puzzleWithOneHole), SOLVED_PUZZLE)
    )
  }

  final class DokuResult(actual: Option[Array[Array[Int]]], expected: Array[Array[Int]])
    extends BenchmarkResult {

    override def validate(): Unit = {
      if (actual.isEmpty) {
        throw new ValidationException("Result array does not exist.")
      }

      for ((expectedSlice, index) <- expected.zipWithIndex) {
        val actualSlice = actual.get(index)
        if (!expectedSlice.sameElements(actualSlice)) {
          throw new ValidationException(
            s"Result row $index does not match the expected solution: actual ${actualSlice.toSeq}, expected ${expectedSlice.toSeq}"
          )
        }
      }
    }
  }

}
