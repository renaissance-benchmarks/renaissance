package cafesat
package theories.adt

import org.scalatest.flatspec.AnyFlatSpec

import scala.reflect.ClassTag

/**
 * Created by gs on 14.05.15.
 */
class AdtSolverNullConstructorsTests extends AnyFlatSpec with AdtSolverSpecHelpers {

  import Types._

  "Solver" should "return sat on empty constraints" in new SimpleFiniteSig {
    assertSat()
  }

  it should "return sat on trivial constraints" in new SimpleFiniteSig {
    // TODO: This case (any many other simple ones) should work without splitting as
    //  soon as inequality detection has been improved
//    override val expectSplitting = Some(false)
    override val eqs = Seq((Variable(1), Variable(1)))
    assertSat()
  }

  it should "return unsat on trivial inequality" in new SimpleFiniteSig {
    override val ineqs = Seq((Variable(1), Variable(1)))
    assertUnsatDueTo[InvalidEquality]()
  }

  it should "return sat on trivial unification" in new SimpleFiniteSig {
    override val eqs = Seq((Variable(1), Fina))
    assertSat()
  }
  it should "return sat on trivial multiple unification" in new SimpleFiniteSig {
    override val eqs = Seq((Variable(1), Fina), (Variable(2), Finb))
    assertSat()
  }

  it should "return sat on trivial equality of constructors" in new SimpleFiniteSig {
    override val eqs = Seq((Finb, Finb))
    assertSat()
  }

  it should "return unsat on trivially distinct constructors" in new SimpleFiniteSig {
    override val eqs = Seq((Fina, Finb))
    assertUnsatDueTo[EmptyLabelling]()
  }

  it should "return unsat on simply distinct constructors 1" in new SimpleFiniteSig {
    override val eqs = Seq((Variable(1), Fina), (Variable(1), Finb) )
    assertUnsatDueTo[EmptyLabelling]()
  }
  it should "return unsat on simply distinct constructors 2" in new SimpleFiniteSig {
    override val eqs = Seq((Variable(1), Fina), (Finb, Variable(1)) )
    assertUnsatDueTo[EmptyLabelling]()
  }
  it should "return unsat on simple inequality" in new SimpleFiniteSig {
    override val eqs = Seq((Variable(1), Fina), (Variable(2), Fina) )
    override val ineqs = Seq((Variable(1), Variable(2)))
    assertUnsatDueTo[InvalidEquality]()
  }

  it should "return unsat on distinct constructors with variable equality" in new SimpleFiniteSig {
    override val eqs = Seq(
      (Variable(1), Fina),
      (Variable(2), Finb),
      (Variable(1), Variable(2))
    )
    assertUnsatDueTo[EmptyLabelling]()
  }

  it should "return sat on simple equality 1" in new SimpleFiniteSig {
    override val eqs = Seq((Variable(1), Fina), (Variable(1), Fina) )
    assertSat()
  }
  it should "return sat on simple equality 2" in new SimpleFiniteSig {
    override val eqs = Seq(
      (Variable(1), Fina),
      (Variable(2), Fina),
      (Variable(1), Variable(2))
    )
    assertSat()
  }

  trait SingleConstructorSig extends FreshSolver {
    val Fina = Constructor(0,0,List())
  
    val sigFin = Seq(Seq())
    val sigFinDts = Seq(Seq())
    val sig = Signature(Seq(sigFin), Seq(sigFinDts))
  }

  it should "return unsat with 2 variables ineqs on a sort with a single value" in new SingleConstructorSig {
    val x = Variable(1)
    val y = Variable(2)
    override val ineqs = Seq((x,y))
    assertUnsat()
  }
  it should "return sat with 2 variables eqs on a sort with a single value" in new SingleConstructorSig {
    val x = Variable(1)
    val y = Variable(2)
    override val eqs = Seq((x,y))
    assertSat()
  }
  it should "return unsat with 3 distinct variables on a sort with two values" in new SimpleFiniteSig {
    val x = Variable(1)
    val y = Variable(2)
    val z = Variable(2)
    override val ineqs = Seq((x,y), (y,z), (x, z))
    assertUnsat()
  }
  it should "return sat with 2 distinct variables on a sort with two values" in new SimpleFiniteSig {
    val x = Variable(1)
    val y = Variable(2)
    override val ineqs = Seq((x,y))
    assertSat()
  }

}
