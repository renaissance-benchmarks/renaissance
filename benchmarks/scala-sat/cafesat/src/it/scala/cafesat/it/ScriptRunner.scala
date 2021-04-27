package cafesat
package it

import scala.sys.process._

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

import java.io.File
import java.io.FileReader

import parsers.Dimacs

class Tests extends AnyFunSuite with Matchers {

  private implicit val testingContext = Context(logger=util.SilentLogger)

  val all: String => Boolean = (s: String) => true
  val resourceDirHard = "src/it/resources/"

  def filesInResourceDir(dir : String, filter : String=>Boolean = all) : Iterable[File] = {    
    import scala.jdk.CollectionConverters._
    val d = this.getClass.getClassLoader.getResource(dir)
    val asFile = if(d == null || d.getProtocol != "file") {
      // We are in Eclipse. The only way we are saved is by hard-coding the path               
      new File(resourceDirHard + dir)
    } else new File(d.toURI())
    asFile.listFiles().filter(f => filter(f.getPath()))
  }

  filesInResourceDir("regression/dimacs/sat", _.endsWith(".cnf")).foreach(file => {
    test("Checking SAT solver on sat instance: " + file.getPath) {
      val res = runSatSolver(file)
      res shouldBe a [sat.Solver.Results.Satisfiable]
    }
  })

  filesInResourceDir("regression/dimacs/unsat", _.endsWith(".cnf")).foreach(file => {
    test("Checking SAT solver on unsat instance: " + file.getPath) {
      val res = runSatSolver(file)
      res shouldBe sat.Solver.Results.Unsatisfiable
    }
  })

  filesInResourceDir("regression/dimacs/sat", _.endsWith(".cnf")).foreach(file => {
    test("Checking DPLL(T) SAT solver on sat instance: " + file.getPath) {
      val res = runDpllTSatSolver(file)
      res shouldBe a [dpllt.DPLLSolver.Results.Satisfiable]
    }
  })

  filesInResourceDir("regression/dimacs/unsat", _.endsWith(".cnf")).foreach(file => {
    test("Checking DPLL(T) SAT solver on unsat instance: " + file.getPath) {
      val res = runDpllTSatSolver(file)
      res shouldBe dpllt.DPLLSolver.Results.Unsatisfiable
    }
  })


  def runSatSolver(file: File): sat.Solver.Results.Result = {
    import sat._

    val (satInstance, nbVars) = Dimacs.cnf(new FileReader(file))
    val s = new Solver(nbVars)

    satInstance.foreach(s.addClause(_))
    val result = s.solve()
    result
  }

  def runDpllTSatSolver(file: File): dpllt.DPLLSolver.Results.Result = {
    val (satInstance, nbVars) = Dimacs.cnf(new FileReader(file))
    val s = new dpllt.DPLLSolver[dpllt.BooleanTheory.type](nbVars, dpllt.BooleanTheory)
    val cnf = satInstance.map(clause => {
      val lits: Set[s.theory.Literal] =
        clause.map(l => dpllt.BooleanTheory.PropositionalLiteral(l.getID, if(l.polarity) 1 else 0))
      lits
    }).toSet
    cnf.foreach(lits => s.addClause(lits))
    val result = s.solve(dpllt.BooleanTheory.makeSolver(cnf))
    result
  }

}
