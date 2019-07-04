package cafesat
package theories.adt

import Types._

//TODO: maybe add a ConstructorSig(sorts: Seq[SortRef]) and use it in Signature?
//      case class Signature(sorts: Seq[Seq[ConstructorSig]], ...)

/*
 * designatedTerms (also called distinguished terms), are used when a selector is applied
 * to a wrong constructor (with correct sort, but wrong constructor). For example:
 *   type A = A1 (s1: Nat) | A2 (s2: Nat)
 *   s1(x) = y && s2(x) = z
 * the above is a valid input for the solver (but probably not in a programming language
 * as selectors would not type check unless we know that x is of the specific constructor
 * type), and will actually be SAT as the solver will choose to use the distinguished term
 * for one of the selector (if x is decided to be A1, then we will use designated term for
 * selector s2 when applied to x). Adding further constraint to prevent values from taking
 * one of the designated terms values would make this unsat as well. It means, it should
 * be possible to extend the procedure to always return unsat on non well-typed formulas
 * like the above.
 *
 * Note that this is very different from a sort error, where we have type A, and type B,
 * and x is used with a selector in type A and in type B, which is not supported by
 * the procedure and should be caught statically (usually, variable have a declared sort).
 */

// Signature =^ seq of sorts, sort =^ seq of ctors, ctor =^ seq of arg. sorts
case class Signature(sorts: Seq[Seq[Seq[SortRef]]], designatedTerms: Seq[Seq[Seq[Term]]]) {
  val sortRefs: Seq[SortRef] = (0 until sorts.size).toSeq

  require(Signature.isWellFounded(sorts))

  require(sorts forall { ctors =>
    ctors forall { args =>
      args forall sortRefs.contains
    }
  })
  // Check that designatedTerms is of the same shape as sorts
  require(designatedTerms.size == sorts.size &&
    designatedTerms.zipWithIndex.forall { case (ofSort, sort) =>
      ofSort.size == sorts(sort).size &&
        ofSort.zipWithIndex.forall { case (ofCtor, ctor) =>
          ofCtor.size == sorts(sort)(ctor).size
        }
      })

  // FIXME: Inefficient to generate Sets here.
  def ctorRefs(sort: SortRef): CtorRefSet = {
    // sort \in sortRefs
    val ctors = (0 until sorts(sort).size).toSet
    newCtorRefSet(ctors)
  }
  def argIndices(sort: SortRef, ctor: CtorRef): Seq[Index] = {
    // sort \in sortRefs, ctor in \in ctorRefs(sort)
    (0 until sorts(sort)(ctor).size).toSeq
  }
  def argSort(sort: SortRef, ctor: CtorRef, index: Index): SortRef = {
    // sort \in sortRefs, ctor in \in ctorRefs(sort),
    //  index \in argIndices(sort, ctor)
    sorts(sort)(ctor)(index)
  }

  def isNullaryCtor(sort: SortRef, ctor: CtorRef): Boolean =
    sorts(sort)(ctor).isEmpty

  def isFiniteSort(sort: SortRef, from: Set[SortRef] = Set.empty): Boolean = {
    (0 until sorts(sort).size) forall (isFiniteCtor(sort, _, from))
  }

  def isFiniteCtor(sort: SortRef, ctor: CtorRef,
                   from0: Set[SortRef] = Set.empty): Boolean = {
    val argSorts = sorts(sort)(ctor)
    val from = from0 + sort
    argSorts.isEmpty ||
      (argSorts forall (as => !from.contains(as) && isFiniteSort(as, from)))
  }

  // Designated terms for selectors applied to terms of the 'wrong' sort/ctor
  def allDesignatedTerms(): Seq[Term] =
    designatedTerms flatMap { _ flatMap identity }
}

object Signature {

  /** Check that the set of RDTs is well-founded
    *
    * To be well-founded, We need each RDT to have at least a
    * base value (a null constructor, or all subterms of well-sorted sort).
    * All the non RDTs sorts are well-founded.
    *
    * The solver assumes that the signature is well-founded, so the client
    * should make sure it sends a well-founded signature.
    *
    * TODO: take into account the non RDTs sorts, maybe using negative index for SortRef?
    */
  def isWellFounded(sig: Seq[Seq[Seq[SortRef]]]): Boolean = {
    import scala.collection.mutable.HashSet
    val sortWellFounded: Array[Boolean] = Array.fill(sig.size)(false)

    var converged = false
    while(!converged) {
      converged = true
      var refined = false
      for(i <- 0 until sig.size) {
        if(!sortWellFounded(i)) {
          converged = false
          val ctors: Seq[Seq[SortRef]] = sig(i)
          if(ctors.exists(ctor => ctor.forall(sort => sortWellFounded(sort)))) {
            sortWellFounded(i) = true
            refined = true
          }
        }
      }
      if(!converged && !refined)
        return false
    }
    true
  }

}
