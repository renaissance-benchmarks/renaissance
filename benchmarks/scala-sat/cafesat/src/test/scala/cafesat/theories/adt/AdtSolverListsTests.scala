package cafesat
package theories.adt

import org.scalatest._
import org.scalatest.flatspec.AnyFlatSpec

import scala.reflect.ClassTag

class AdtSolverListsTests extends AnyFlatSpec with BeforeAndAfter with AdtSolverSpecHelpers {

  //TODO: could be useful to have that for debugging
  //private var _currentTestName: String = "<Unset>"
  //def currentTestName = "unknown"//_currentTestName
  //override protected def runTest(testName: String, reporter: Reporter,
  //                                stopper: Stopper, configMap: Map[String, Any],
  //                                tracker: Tracker): Unit = {
  //  _currentTestName = testName
  //  super.runTest(testName, reporter, stopper, configMap, tracker)
  //}

  //before {
  //  println(s"== $currentTestName ==")
  //}
  //after {
  //  println("")
  //}


  import Types._

  trait FiniteAndListSig extends SimpleFiniteSig {
    def Cons(h: Term, t:Term) = Constructor(1,0,List(h,t))
    val Nil = Constructor(1,1,List())
    def Head(cons: Term) = Selector(1,0,0,cons)
    def Tail(cons: Term) = Selector(1,0,1,cons)
    
    def IsCons(t: Term): Tester = Tester(1,0,t)
    def IsNil(t: Term): Tester = Tester(1,1,t)

    def TailN(n: Int, base: Term): Term = n match {
      case 0 => base
      case 1 => Tail(base)
      case i => Tail(TailN(i-1, base))
    }
  
    val sigList = Seq(Seq(0,1), Seq()) // Cons(Fin, List), Nil
    val sigListDts = Seq(Seq(Nil, Nil), Seq())
    override val sig = Signature(Seq(sigFin, sigList), Seq(sigFinDts, sigListDts))
  }

  "Solver" should "return sat on empty constraints" in new FiniteAndListSig {
    assertSat()
  }

  it should "return sat on equality of empty lists" in new FiniteAndListSig {
    override val eqs = Seq( (Nil, Nil) )
    assertSat()
  }
  it should "return sat on list with same constants" in new FiniteAndListSig {
    override val eqs = Seq( (Cons(Fina,Nil), Cons(Fina,Nil)) )
    assertSat()
  }
  it should "return unsat on list with different constants" in new FiniteAndListSig {
    override val eqs = Seq( (Cons(Fina,Nil), Cons(Finb,Nil)) )
    assertUnsat()
  }
  it should "return unsat when x is two different constructors" in new FiniteAndListSig {
    val x = Variable(1)
    val y = Variable(2)
    val z = Variable(3)
    override val eqs = Seq( (x, Cons(y,z)), (x, Nil) )
    assertUnsatDueTo[EmptyLabelling]()
  }
  it should "return unsat when x=y but two different constructors" in new FiniteAndListSig {
    val x = Variable(1)
    val y = Variable(2)
    val z = Variable(3)
    val z2 = Variable(4)
    override val eqs = Seq( (x, Cons(z,z2)), (y, Nil), (x,y) )
    assertUnsatDueTo[EmptyLabelling]()
  }

  it should "return sat on list equality with variables" in new FiniteAndListSig {
    val x = Variable(1)
    val y = Variable(2)
    override val eqs = Seq( (Cons(x,Nil), Cons(y,Nil)) )
    assertSat()
  }

  it should "return unsat on list inequality with variable" in new FiniteAndListSig {
    val x = Variable(1)
    val y = Variable(2)
    override val eqs = Seq( (Cons(x,Nil), Cons(y,Nil)) )
    override val ineqs = Seq( (x,y) )
    assertUnsatDueTo[InvalidEquality]()
  }

  it should "return unsat on list cycle" in new FiniteAndListSig {
    val x = Variable(1)
    val y = Variable(2)
    override val eqs = Seq( (Cons(x,y), y) )
    assertUnsatDueTo[Cyclic]()
  }
  it should "return unsat on list cycle with inconsistant variables" in new FiniteAndListSig {
    val x = Variable(1)
    override val eqs = Seq( (Cons(x,Nil), x) )
    assertUnsatDueTo[Cyclic]()
  }

  it should "return sat on list len [_] <= len [_,_]" in new FiniteAndListSig {
    val x = Variable(1)
    override val eqs = Seq( (Cons(Fina,x), Cons(Fina,Cons(Fina,Nil))) )
    assertSat()
  }
  it should "return unsat on list len [_,_] <= len [_]" in new FiniteAndListSig {
    val x = Variable(1)
    override val eqs = Seq( (Cons(Fina,Nil), Cons(Fina,Cons(Fina,x))) )
    assertUnsatDueTo[EmptyLabelling]()
  }
  it should "return sat on list with variable equals Nil" in new FiniteAndListSig {
    val x = Variable(1)
    override val eqs = Seq( (Cons(Fina,x), Cons(Fina,Nil)) )
    assertSat()
  }

  it should "return unsat on trivial selector inequality" in new FiniteAndListSig {
    val x = Variable(1)
    override val eqs = Seq( (Head(x), Fina) )
    override val ineqs = Seq( (Head(x), Fina) )
    assertUnsatDueTo[InvalidEquality]()
  }
  it should "return unsat on simple selector inequality" in new FiniteAndListSig {
    val x = Variable(1)
    override val eqs = Seq( (x, Cons(Fina,Nil)) )
    override val ineqs = Seq( (Head(x), Fina) )
    assertUnsatDueTo[InvalidEquality]()
  }
  it should "return sat on list equality with selectors" in new FiniteAndListSig {
    val x = Variable(1)
    val y = Variable(2)
    override val eqs = Seq( (x, Cons(y,Nil)), (Head(x), y), (Tail(x), Nil) )
    assertSat()
  }

  it should "return unsat on simple instantiation of Cons, no merge, no splitting" in new FiniteAndListSig {
    val x = Variable(1)
    override val eqs = Seq( (Head(x), Fina), (Tail(x), Nil) )
    override val ineqs = Seq( (x, Cons(Fina,Nil)) )
    override val tests = Seq( IsCons(x) )
    assertUnsatDueTo[InvalidEquality]()
  }
  it should "return unsat on simple instantiation of Cons, with merge, no splitting" in new FiniteAndListSig {
    val x = Variable(1)
    val y = Variable(2)
    override val eqs = Seq( (Head(x), Fina), (Tail(y), Nil), (x,y) )
    override val ineqs = Seq( (x, Cons(Fina,Nil)) )
    override val tests = Seq( IsCons(x) )
    assertUnsatDueTo[InvalidEquality]()
  }
  it should "return unsat on simple instantiation of Cons, with merge, no splitting, free var" in new FiniteAndListSig {
    val x = Variable(1)
    val y = Variable(2)
    val z = Variable(3)
    override val eqs = Seq( (Head(x), z), (Tail(y), Nil), (x,y) )
    override val ineqs = Seq( (x, Cons(z,Nil)) )
    override val tests = Seq( IsCons(x) )
    assertUnsatDueTo[InvalidEquality]()
  }
  it should "return unsat on simple instantiation of Cons, with splitting" in new FiniteAndListSig {
//    solver.debugOn
    override val expectSplitting = Some(true)
    val x = Variable(1)
    val z = Variable(3)
    override val eqs = Seq( (Head(x), z), (Tail(x), Nil) )
    override val ineqs = Seq( (x, Cons(z,Nil)) )
    //assertUnsatDueTo[InvalidEquality]()
    assertUnsat()
  }

  it should "return unsat on degenerate cyclic list example" in new FiniteAndListSig {
//    solver.debugOn
    override val expectSplitting = Some(true)
    val x = Variable(1)
    val z = Variable(3)
    override val eqs = Seq( (TailN(2,z), x), (z, x) )
    override val tests = Seq( IsCons(z) )
    assertUnsat()
  }

  // TODO: Test case to check Instantiate 2 rule

  it should "return unsat on deep cycle of tails, with splitting" in new FiniteAndListSig {
    override val expectSplitting = Some(true)
    val x = Variable(1)
    val z = Variable(3)
    override val eqs = Seq((TailN(20,z), x), (z,x))
    override val tests = Seq(IsCons(z))
    assertUnsat()
  }

  it should "return unsat on inconsistent inequality between two lists when one is defined implicitly by its selectors" in new FiniteAndListSig {
    val x = Variable(1)
    val y = Variable(2)
    val z = Variable(3)
    val w = Variable(4)
    override val eqs = Seq((Cons(x,y), z), (Head(w), x), (Tail(w), y))
    override val ineqs = Seq((w, z))
    //TODO: should not need the tests, but they work while the test crashes without
    //override val tests = Seq(IsCons(w)) 
    assertUnsat()
  }

  it should "return unsat on two implicit cons defined with selectors with an inconsistent inequality" in new FiniteAndListSig {
    val x = Variable(1)
    val y = Variable(2)
    val z = Variable(3)
    val v = Variable(4)
    val w = Variable(5)
    override val eqs = Seq((Cons(x,y), z), (Head(w), x), (Tail(w), y), (v, w))
    override val ineqs = Seq((y, Tail(v)))
    assertUnsat()
  }

  it should "return unsat on a cycle with indirect equality between the lists" in new FiniteAndListSig {
    val x = Variable(1)
    val y = Variable(2)
    val w = Variable(3)
    override val eqs = Seq((Cons(x,y), w), (Tail(w), Tail(y)))
    override val ineqs = Seq((y, Nil))
    assertUnsat()
  }

}
