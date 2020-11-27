package cafesat
package theories.adt

import org.scalatest.flatspec.AnyFlatSpec

import scala.reflect.ClassTag

class AdtSolverMultiConstructorsTests extends AnyFlatSpec with AdtSolverSpecHelpers {

  import Types._

  trait FiniteAndMultiCtors extends SimpleFiniteSig {
    def C1(t: Term) = Constructor(1,0,List(t))
    def C2(t: Term) = Constructor(1,1,List(t))

    def S1(c1: Term) = Selector(1,0,0,c1)
    def S2(c2: Term) = Selector(1,1,0,c2)

    def IsC1(t: Term) = Tester(1,0,t)
    def IsC2(t: Term) = Tester(1,1,t)
  
    val sigMulti = Seq(Seq(0), Seq(0)) // C1(Fin), C2(Fin)
    val sigMultiDts = Seq(Seq(Fina), Seq(Finb))
    override val sig = Signature(Seq(sigFin, sigMulti), Seq(sigFinDts, sigMultiDts))
  }

  "Solver" should "return sat on empty constraints" in new FiniteAndMultiCtors {
    assertSat()
  }

  it should "return sat on trivial constraints" in new FiniteAndMultiCtors {
    override val eqs = Seq((Variable(1), Variable(1)))
    assertSat()
  }

  it should "return sat when same constructor" in new FiniteAndMultiCtors {
    val x = Variable(1)
    val y = Variable(2)
    val z = Variable(3)
    override val eqs = Seq((C1(x), z), (C1(y), z))
    assertSat()
  }

  it should "return unsat when same constructor but arguments differ" in new FiniteAndMultiCtors {
    val x = Variable(1)
    val y = Variable(2)
    val z = Variable(3)
    override val eqs = Seq((C1(x), z), (C1(y), z))
    override val ineqs = Seq((x, y))
    assertUnsatDueTo[InvalidEquality]()
  }

  it should "return sat when different constructors are used differently" in new FiniteAndMultiCtors {
    val x = Variable(1)
    val y = Variable(2)
    val z = Variable(3)
    override val eqs = Seq((C1(x), y), (C2(x), z))
    assertSat()
  }

  it should "return unsat when different constructors" in new FiniteAndMultiCtors {
    val x = Variable(1)
    val y = Variable(2)
    val z = Variable(3)
    override val eqs = Seq((C1(x), z), (C2(y), z))
    assertUnsatDueTo[EmptyLabelling]()
  }

  //This is quite tricky, we are using x with S1 and S2, meaning that intuitively there
  //should not be such an x (cannot be both of C1 and C2 constructor), but according to
  //the rules and the usual semantics of ADTs, this should actually be SAT. This is
  //due to selectors being partial functions, but being extended to a total function via
  //a distinguished term, which means that it is ok to apply to wrong constructors.
  it should "return sat when x is used with different selectors" in new FiniteAndMultiCtors {
    override val expectSplitting = Some(true)
    val x = Variable(1)
    val y = Variable(2)
    val z = Variable(3)
    override val eqs = Seq((S1(x), y), (S2(x), z))
    assertSat()
  }

  //still sat, for similar reason as above
  it should "return sat when x is used with different selectors and tester forces one" in new FiniteAndMultiCtors {
    override val expectSplitting = Some(true)
    val x = Variable(1)
    val y = Variable(2)
    val z = Variable(3)
    override val eqs = Seq((S1(x), y), (S2(x), z))
    override val tests = Seq( IsC1(x) )
    assertSat()
  }

  it should "return sat when x is used with different selectors and one is different from distinguished term" in new FiniteAndMultiCtors {
    override val expectSplitting = Some(true)
    val x = Variable(1)
    val y = Variable(2)
    val z = Variable(3)
    override val eqs = Seq((S1(x), y), (S2(x), z), (z, Fina))
    assertSat()
  }

  //but that one should be unsat, because we force x to be C1, meaning that S2(x) will
  //work but be assigned to the distinguished term (Finb), and we finally force z to
  //be Fina.
  it should "return unsat when x is used with different selectors and result differ from distinguished term" in new FiniteAndMultiCtors {
    val x = Variable(1)
    val y = Variable(2)
    val z = Variable(3)
    override val eqs = Seq((S1(x), y), (S2(x), z), (z, Fina))
    override val tests = Seq( IsC1(x) )
    assertUnsat()
  }

  it should "return sat when an equivalent variable is used with incompatible selectors" in new FiniteAndMultiCtors {
    val x = Variable(1)
    val y = Variable(2)
    val z = Variable(3)
    val z2 = Variable(4)
    override val eqs = Seq((S1(z), x), (S2(z2), y), (z, z2))
    assertSat()
  }
  it should "return unsat when an equivalent variable is used with incompatible selectors and forced different from distinguished term" in new FiniteAndMultiCtors {
    val x = Variable(1)
    val y = Variable(2)
    val z = Variable(3)
    val z2 = Variable(4)
    override val eqs = Seq((S1(z), x), (S2(z2), y), (z, z2), (y, Fina))
    override val tests = Seq(IsC1(z))
    assertUnsat()
  }

}
