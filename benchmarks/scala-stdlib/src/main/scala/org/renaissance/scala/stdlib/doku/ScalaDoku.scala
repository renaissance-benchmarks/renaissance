package org.renaissance.scala.stdlib.doku

import cafesat.api.FormulaBuilder.{and, or, propVar}
import cafesat.api.Solver.solveForSatisfiability
import org.renaissance.Benchmark._
import org.renaissance.{
  BenchmarkResult,
  CompoundResult,
  Config,
  EmptyResult,
  License,
  RenaissanceBenchmark,
  ValidationException
}

object Solver {

  /** Solver take a sudoku problem as a matrix of optional int,
   *  its goal is to fill out the matrix with missing integer
   *  to form a correct sudoku grid.
   */
  def solve(sudoku: Array[Array[Option[Int]]]): Option[Array[Array[Int]]] = {

    /** Each slot on the sudoku board has 9 variables V0..V8 associated with it,
     *  each variable Vi denoting whether the digit Vi was chosen for the respective slot.
     */
    require(sudoku.size == 9)
    require(sudoku.forall(row => row.size == 9))

    val vars = sudoku.map(row => row.map(el => Array.fill(9)(propVar())))

    /** There should be at least one digit chosen for each sudoku slot.
     */
    val onePerEntry = vars.flatMap(row => row.map(vs => or(vs: _*)))

    /**
     * There must be at most one any digit in each 3x3 table.
     * Here, `k` is the variable (digit), `i` and `j` are the coordinates of the 3x3 tables,
     * `r1` and `r2` are row pairs within the 3x3 table, and `c1` and `c2` are pairs of
     * columns within the 3x3 table.
     */
    val uniqueInGrid1 =
      for (k <- 0 to 8; i <- 0 to 2; j <- 0 to 2; r <- 0 to 2;
           c1 <- 0 to 1; c2 <- c1 + 1 to 2)
        yield !vars(3 * i + r)(3 * j + c1)(k) || !vars(3 * i + r)(3 * j + c2)(k)

    val uniqueInGrid2 =
      for (k <- 0 to 8; i <- 0 to 2; j <- 0 to 2; r1 <- 0 to 2;
           c1 <- 0 to 2; c2 <- 0 to 2; r2 <- r1 + 1 to 2)
        yield !vars(3 * i + r1)(3 * j + c1)(k) || !vars(3 * i + r2)(3 * j + c2)(k)

    /**
     * In the respective column, there should be at most one unique digit.
     */
    val uniqueInColumns = for (c <- 0 to 8; k <- 0 to 8; r1 <- 0 to 7; r2 <- r1 + 1 to 8)
      yield !vars(r1)(c)(k) || !vars(r2)(c)(k)

    /**
     * In the respective row, there should be at most one unique digit.
     */
    val uniqueInRows = for (r <- 0 to 8; k <- 0 to 8; c1 <- 0 to 7; c2 <- c1 + 1 to 8)
      yield !vars(r)(c1)(k) || !vars(r)(c2)(k)

    /**
     * Force entry with a possible number.
     */
    val forcedEntries = for (r <- 0 to 8; c <- 0 to 8 if sudoku(r)(c) != None)
      yield or(vars(r)(c)(sudoku(r)(c).get - 1))

    /**
     * All constraints for a soduko problem.
     */
    val allConstraints = onePerEntry ++ uniqueInColumns ++ uniqueInRows ++
      uniqueInGrid1 ++ uniqueInGrid2 ++ forcedEntries

    /**
     * The whole grid should Satisfy all constraints.
     */
    solveForSatisfiability(and(allConstraints: _*))
      .map(model => vars.map(row => row.map(vs => vs.indexWhere(v => model(v)) + 1)))
  }

}

@Name("scala-doku")
@Group("scala-stdlib")
@Summary("Solves Sudoku Puzzles using Scala collections.")
@Licenses(Array(License.MIT))
@Repetitions(10)
class ScalaDoku extends RenaissanceBenchmark {

  class DokuResult(actualResult: Array[Array[Int]], expectedResult: Array[Array[Int]])
    extends BenchmarkResult {
    override def validate(): Unit = {
      if (expectedResult.deep != actualResult.deep)
        throw new ValidationException("Result array differs from expected solution.")
    }
  }

  /*
   * An arbitrary solved sudoku puzzle. The puzzle is copied and some entries
   * are changed to have an unsolved version for the algorithm to solve it again.
   */
  val SOLVED_PUZZLE = Array(
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

  var puzzle1: Array[Array[Option[Int]]] = null

  var puzzle2: Array[Array[Option[Int]]] = null

  private def preparePuzzleWithAFewHoles(): Unit = {
    puzzle1 = SOLVED_PUZZLE.map(row => row.map(i => (Some(i): Option[Int])))
    puzzle1(0)(0) = None
    puzzle1(4)(8) = None
    puzzle1(7)(7) = None
  }

  private def preparePuzzleWithOneHole(): Unit = {
    puzzle2 = SOLVED_PUZZLE.map(row => row.map(i => (Some(i): Option[Int])))
    puzzle2(2)(7) = None
  }

  override def setUpBeforeAll(c: Config): Unit = {
    preparePuzzleWithAFewHoles()
    preparePuzzleWithOneHole()
  }

  private def validateResultExists(result: Option[Array[Array[Int]]]): Array[Array[Int]] = {
    if (result == None)
      throw new ValidationException("Result array does not exist.")
    return result.get
  }

  private def solvePuzzleWithAFewHoles(): Array[Array[Int]] = {
    return validateResultExists(Solver.solve(puzzle1))
  }

  private def solvePuzzleWithOneHole(): Array[Array[Int]] = {
    return validateResultExists(Solver.solve(puzzle2))
  }

  override def runIteration(c: Config): BenchmarkResult = {
    return new CompoundResult(
      new DokuResult(solvePuzzleWithAFewHoles(), SOLVED_PUZZLE),
      new DokuResult(solvePuzzleWithOneHole(), SOLVED_PUZZLE)
    )
  }
}
