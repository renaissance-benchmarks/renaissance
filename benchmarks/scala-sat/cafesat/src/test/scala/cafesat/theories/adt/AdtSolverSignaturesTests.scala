package cafesat
package theories.adt

import org.scalatest._

import scala.reflect.ClassTag

class AdtSolverSignaturesTests extends FlatSpec {


  "Enum ADT" should "have a well-founded signature" in {
    val sigFinite1 = Seq(Seq(Seq())) // one sort, one null constructor
    assert(Signature.isWellFounded(sigFinite1))
    val sigFinite2 = Seq(Seq(Seq(), Seq())) //one sort, two null constructors
    assert(Signature.isWellFounded(sigFinite2))
    val sigFinite3 = Seq(Seq(Seq(), Seq()), Seq(Seq())) //two sorts with null constructors
    assert(Signature.isWellFounded(sigFinite3))
  }

  it should "have all sorts finite" in {
    val sigFinite1 = Seq(Seq(Seq()))
    val sig1 = Signature(sigFinite1, Seq(Seq(Seq())))
    assert(sig1.isFiniteSort(0))
    val sigFinite2 = Seq(Seq(Seq(), Seq()))
    val sig2 = Signature(sigFinite2, Seq(Seq(Seq(), Seq())))
    assert(sig2.isFiniteSort(0))
    val sigFinite3 = Seq(Seq(Seq(), Seq()), Seq(Seq()))
    val sig3 = Signature(sigFinite3, Seq(Seq(Seq(), Seq()), Seq(Seq())))
    assert(sig3.isFiniteSort(0))
  }

  "Non recursive ADT" should "have a well-founded signature" in {
    val sigFinite1 = Seq(Seq(Seq()), Seq(Seq(0))) // one base sort, one simple wrapper constructor
    assert(Signature.isWellFounded(sigFinite1))
    val sigFinite2 = Seq(Seq(Seq(1)), Seq(Seq())) // one base sort, one simple wrapper constructor
    assert(Signature.isWellFounded(sigFinite2))
    val sigFinite3 = Seq(Seq(Seq(), Seq()), Seq(Seq(0)))
    assert(Signature.isWellFounded(sigFinite3))
    val sigFinite4 = Seq(Seq(Seq(), Seq(), Seq()), Seq(Seq(0), Seq(0)))
    assert(Signature.isWellFounded(sigFinite4))
  }

  it should "have all sorts finite" in {
    val sigFinite1 = Seq(Seq(Seq()), Seq(Seq(0)))
    val sig1 = Signature(sigFinite1, Seq(Seq(Seq()), Seq(Seq(Constructor(0,0,List())))))
    assert(sig1.isFiniteSort(0))
    assert(sig1.isFiniteSort(1))

    val sigFinite2 = Seq(Seq(Seq(1)), Seq(Seq()))
    val sig2 = Signature(sigFinite2, Seq(Seq(Seq(Constructor(0,0,List()))), Seq(Seq())))
    assert(sig2.isFiniteSort(0))
    assert(sig2.isFiniteSort(1))

    val sigFinite3 = Seq(Seq(Seq(), Seq()), Seq(Seq(0)))
    val sig3 = Signature(sigFinite3, Seq(Seq(Seq(), Seq()), Seq(Seq(Constructor(0,0,List())))))
    assert(sig3.isFiniteSort(0))
    assert(sig3.isFiniteSort(1))

    val sigFinite4 = Seq(Seq(Seq(), Seq(), Seq()), Seq(Seq(0), Seq(0)))
    val sig4 = Signature(sigFinite4, Seq(Seq(Seq(), Seq(), Seq()), 
                                         Seq(Seq(Constructor(0,0,List())), Seq(Constructor(0,0,List())))))
    assert(sig4.isFiniteSort(0))
    assert(sig4.isFiniteSort(1))
  }

  "Recursive ADT" should "be well-founded if it has a base case" in {
    val sigNat = Seq(Seq(Seq(0), Seq()))
    assert(Signature.isWellFounded(sigNat))
    val sigList = Seq(Seq(Seq(), Seq(), Seq()), Seq(Seq(0, 1), Seq()))
    assert(Signature.isWellFounded(sigList))
    val sigTree = Seq(Seq(Seq(), Seq(), Seq()), Seq(Seq(1, 0, 1), Seq()))
    assert(Signature.isWellFounded(sigTree))
  }

  it should "be detected as non well-founded if missing base case" in {
    val sigCycle1 = Seq(Seq(Seq(0)))
    assert(!Signature.isWellFounded(sigCycle1))
    val sigCycle2 = Seq(Seq(Seq(0), Seq(0)))
    assert(!Signature.isWellFounded(sigCycle2))
    val sigCycle3 = Seq(Seq(Seq()), Seq(Seq(1), Seq(1)))
    assert(!Signature.isWellFounded(sigCycle3))
    val sigCycle4 = Seq(Seq(Seq(0)), Seq(Seq(), Seq()))
    assert(!Signature.isWellFounded(sigCycle4))
  }

  it should "not be a finite sort" in {
    val sigNat = Seq(Seq(Seq(0), Seq()))
    val sig1 = Signature(sigNat, Seq(Seq(Seq(Constructor(0,1,List())), Seq())))
    assert(!sig1.isFiniteSort(0))

    val sigList = Seq(Seq(Seq(), Seq(), Seq()), Seq(Seq(0, 1), Seq()))
    val sig2 = Signature(sigList, Seq(Seq(Seq(), Seq(), Seq()),
                                      Seq(Seq(Constructor(0,0,List()), Constructor(1,1,List())), Seq())))
    assert(sig2.isFiniteSort(0))
    assert(!sig2.isFiniteSort(1))
  }

}
