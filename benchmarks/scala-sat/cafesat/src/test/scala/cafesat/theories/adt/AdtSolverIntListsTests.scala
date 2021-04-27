package cafesat
package theories.adt

import org.scalatest.flatspec.AnyFlatSpec

import scala.reflect.ClassTag

class AdtSolverIntListsTests extends AnyFlatSpec with AdtSolverSpecHelpers {

  import Types._

  trait SIntAndIntListSig extends FreshSolver {
    def Succ(pred: Term) = Constructor(0,0,List(pred))
    val Zero = Constructor(0,1,List())
    def Pred(succ: Term) = Selector(0,0,0,succ)
  
    def Cons(h: Term, t:Term) = Constructor(1,0,List(h,t))
    val Nil = Constructor(1,1,List())
    def Head(cons: Term) = Selector(1,0,0,cons)
    def Tail(cons: Term) = Selector(1,0,1,cons)
  
    val sigSInt = Seq(Seq(0), Seq()) // Succ(SInt), Zero
    val sigSIntDts = Seq(Seq(Zero), Seq())
    val sigList = Seq(Seq(0,1), Seq()) // Cons(SInt, List), Nil
    val sigListDts = Seq(Seq(Zero, Nil), Seq())
    override val sig = Signature(Seq(sigSInt, sigList), Seq(sigSIntDts, sigListDts))
  }

  "Solver" should "return sat on our sample for branching" in new SIntAndIntListSig {
    //solver.debugOn
    val x = Variable(1)
    val m = Variable(2)
    val y = Variable(3)
    override val eqs = Seq( (x, Cons(m, y)) )
    override val ineqs = Seq( (m, Zero), (Head(y), Zero) )
    assertSat()
  }

}
