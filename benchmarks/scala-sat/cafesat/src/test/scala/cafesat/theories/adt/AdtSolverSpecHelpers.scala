package cafesat
package theories.adt

import org.scalatest._

import scala.reflect.ClassTag

trait AdtSolverSpecHelpers {
  this: FlatSpec =>

  import Types._

  trait FreshSolver {
    val solver = new AdtSolver
    val sig: Signature
    val declaredTypes: Typing = Map()
    val eqs: Seq[(Term, Term)] = Seq()
    val ineqs: Seq[(Term, Term)] = Seq()
    val tests: Seq[Tester] = Seq()
    val negtests: Seq[Tester] = Seq()
  
    val expectSplitting: Option[Boolean] = None //Some(false)
  
    def checkSplitting() = {
      val didSplit = solver.debugDidSplit()
      if (expectSplitting.exists(_ != didSplit))
        fail(if (didSplit) "Unexpected splitting" else "Expected splitting, but none occurred")
    }
  
    def solve =
      solver.solve(Instance(sig, declaredTypes, eqs, ineqs, tests, negtests))
  
    def assertSat(dumpModel: Boolean = false) = {
      solve match {
        case Unsat(reason) =>
          fail(s"Unexpectedly unsat: $reason\n" + solver.dumpTerms())
        case Sat(model) => // Ok
          if (dumpModel) {
            println(s"Model:")
              //for (terms <- model; termsSorted = terms.sortBy(solver.termNiceness(_)) if terms.size > 1)
              //  println(s"\t${termsSorted.mkString(" = ")}")
            for ((lblOption, terms) <- model; termsSorted = terms.sortBy(solver.termNiceness))
              println(s"\t$lblOption | ${termsSorted.mkString(" = ")}")
          }
      }
      checkSplitting()
    }
    def assertUnsat() = {
      solve match {
        case Sat(_) => fail(s"Unexpectedly sat")
        case _ => // Ok
      }
      checkSplitting()
    }
    def assertUnsatDueTo[T <: UnsatReason]()(implicit ev: ClassTag[T]) = {
      solve match {
        case Sat(_) => fail(s"Unexpectedly sat")
        case Unsat(_: T) => // Ok
        case Unsat(reason) => fail(s"Expected unsat due to $ev, instead got $reason")
      }
      checkSplitting()
    }
  }

  
  trait SimpleFiniteSig extends FreshSolver {
    val Fina = Constructor(0,0,List())
    val Finb = Constructor(0,1,List())
  
    val sigFin = Seq(Seq(), Seq()) // Cona, Conb
    val sigFinDts = Seq(Seq(), Seq())
    val sig = Signature(Seq(sigFin), Seq(sigFinDts))
  }

}
