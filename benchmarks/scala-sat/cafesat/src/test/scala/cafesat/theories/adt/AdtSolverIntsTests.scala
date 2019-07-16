package cafesat
package theories.adt

import org.scalatest._

import scala.reflect.ClassTag

class AdtSolverIntsTests extends FlatSpec with AdtSolverSpecHelpers {

  trait SIntSig extends FreshSolver {
    def Succ(pred: Term) = Constructor(0,0,List(pred))
    val Zero = Constructor(0,1,List())
    def Pred(succ: Term) = Selector(0,0,0,succ)

    def IsSucc(t: Term) = Tester(0,0,t)
  
    val sigSInt = Seq(Seq(0), Seq()) // Succ(SInt), Zero
    val sigSIntDts = Seq(Seq(Zero), Seq())
    override val sig = Signature(Seq(sigSInt), Seq(sigSIntDts))
  }

  "Solver" should "return sat on empty instance" in new SIntSig {
    assertSat()
  }

  it should "return sat on zero = zero" in new SIntSig {
    override val eqs = Seq((Zero, Zero))
    assertSat()
  }
  it should "return sat on zero = zero with indirection" in new SIntSig {
    val n = Variable(1)
    override val eqs = Seq((Zero, n), (n, Zero))
    assertSat()
  }

  it should "return unsat as zero cannot be the successor of n" in new SIntSig {
    val n = Variable(1)
    val m = Variable(2)
    override val eqs = Seq( (m, Succ(n)), (m, Zero) )
    assertUnsatDueTo[EmptyLabelling]()
  }
  it should "return unsat when s(s(n)) = s(n)" in new SIntSig {
    val n = Variable(1)
    val m = Variable(2)
    override val eqs = Seq( (m, Succ(Succ(n))), (m, Succ(n)) )
    assertUnsatDueTo[Cyclic]()
  }

  it should "return sat with simple but deep term equality" in new SIntSig {
    val x = Variable(1)
    val y = Variable(2)

    override val eqs = Seq((Succ(Succ(Succ(Succ(x)))), Succ(Succ(Succ(Succ(y))))), (x, y))
    assertSat()
  }
  it should "return unsat with deep congruence of different elements" in new SIntSig {
    val x = Variable(1)
    val y = Variable(2)

    override val eqs = Seq((Succ(Succ(Succ(Succ(x)))), Succ(Succ(Succ(Succ(y))))))
    override val ineqs = Seq((x, y))
    assertUnsat()
  }
  it should "return sat with deep term equality split accross several parts" in new SIntSig {
    val x = Variable(1)
    val y = Variable(2)
    val z = Variable(3)

    override val eqs = Seq(
      (Succ(Succ(Succ(Succ(x)))), Succ(Succ(y))),
      (y, Succ(Succ(z))),
      (x, z)
    )
    assertSat()
  }
  it should "return unsat with deep term equality split accross several parts with base distinct" in new SIntSig {
    val x = Variable(1)
    val y = Variable(2)
    val z = Variable(3)

    override val eqs = Seq(
      (Succ(Succ(Succ(Succ(x)))), Succ(Succ(y))),
      (y, Succ(Succ(z)))
    )
    override val ineqs = Seq((x, z))
    assertUnsat()
  }

  it should "return unsat with indirect cycle through many successors" in new SIntSig {
    val x1 = Variable(1)
    val x2 = Variable(1)
    val x3 = Variable(1)
    val x4 = Variable(1)
    val x5 = Variable(1)
    val y = Variable(2)
    val z = Variable(3)

    override val eqs = Seq((Succ(x1), x2), (Succ(x2), x3), (Succ(x3), x4), (Succ(x4), x5), (x5, x1))
    assertUnsatDueTo[Cyclic]()
  }

  //this one is weird, but is sat due to the interpretation of the selector pred on zero
  it should "return sat when y is successor of x but both pred can be equals" in new SIntSig {
    val x = Variable(1)
    val y = Variable(2)

    override val eqs = Seq((Succ(x), y), (Pred(y), Pred(x)))
    assertSat()
  }

  it should "return unsat when y is successor of an isSucc and pred are equals" in new SIntSig {
    val x = Variable(1)
    val y = Variable(2)

    override val eqs = Seq((Succ(x), y), (Pred(y), Pred(x)))
    override val tests = Seq(IsSucc(x))
    assertUnsat()
  }

  it should "return unsat when y is successor of x non-zero and pred are equals" in new SIntSig {
    solver.debug = true
    val x = Variable(1)
    val y = Variable(2)

    override val eqs = Seq((Succ(x), y), (Pred(y), Pred(x)))
    override val ineqs = Seq((x, Zero))
    assertUnsat()
  }
}
