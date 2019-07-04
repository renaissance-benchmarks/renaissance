package cafesat
package theories.adt

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer
import scala.util.control.Breaks._

/**
 * Created by Georg Schmid on 24.04.15.
 *
 * An implementation of the decision procedure for abstract datatypes described
 *  in "An Abstract Decision Procedure for Satisfiability in the Theory of
 *  Recursive Data Types" by Barret et al.
 * Parts of the implementation that correspond to rules described in the paper
 *  are headed by comments of form "// [*Rule*]".
 */

object Types {

  type Index      = Int
  type CtorRef    = Int
  type SortRef    = Int
  type TermRef    = Int
  type CtorRefSet = mutable.BitSet
  type VarId      = Int
  type ConstId    = Int
  type Labels     = Option[(SortRef, CtorRefSet)]
  type Typing     = Map[Term, SortRef]

  def newCtorRefSet(sorts: Set[CtorRef]): CtorRefSet = {
    new mutable.BitSet ++ sorts
  }
}

import Types._

case class Instance(sig: Signature,
                    declaredTypes: Typing,
                    eqs: Seq[(Term, Term)], ineqs: Seq[(Term, Term)],
                    tests: Seq[Tester], negtests: Seq[Tester]) {
  def allTopLevelTerms =
    (eqs ++ ineqs).foldLeft(Seq[Term]()){
      case (seq, (s, t)) => s +: t +: seq
    } ++ (tests ++ negtests).foldLeft(Seq[Term]()){
      case (seq, Tester(_, _, t)) => t +: seq
    }
}

sealed abstract class Term {
  def subTerms = Seq[Term]()
}
case class Variable(varId: VarId) extends Term
case class Constant(constId: ConstId) extends Term
case class Constructor(sort: SortRef, ctor: CtorRef,
                       args: List[Term]) extends Term {
  override def subTerms = args.toSeq
}
case class Selector(sort: SortRef, ctor: CtorRef,
                    index: Index, arg: Term) extends Term {
  override def subTerms = Seq(arg)
}

case class Tester(sort: SortRef, ctor: CtorRef, arg: Term)


abstract class Result
case class Sat(model: Seq[(Option[(SortRef, CtorRef)], Seq[Term])]) extends Result
// NOTE: The UnsatReason is only meaningful when no splitting was required.
case class Unsat(reason: UnsatReason) extends Result

sealed trait UnsatReason
case class Clash(ri: TermRef, rj: TermRef) extends UnsatReason
case class Cyclic(ri: TermRef, rj: TermRef) extends UnsatReason
case class EmptyLabelling(r: TermRef) extends UnsatReason
case class InvalidEquality(i: TermRef, j: TermRef) extends UnsatReason


class AdtSolver {

  case class State(
    nextTermId: TermRef, maxVarId: VarId,
    terms: ArrayBuffer[Term], termRefs: mutable.HashMap[Term, TermRef],
    eqClasses: ArrayBuffer[TermRef], eqClassSizes: ArrayBuffer[Int],
    eqClassConsts: ArrayBuffer[Option[ConstId]], labels: ArrayBuffer[Labels],
    outEdges: ArrayBuffer[ArrayBuffer[TermRef]],
    inEdges: ArrayBuffer[mutable.HashSet[TermRef]],
    sharedSets: mutable.HashMap[(TermRef, TermRef), mutable.HashSet[Index]],
    selectorsOf: mutable.HashMap[TermRef, SelectorMap],
    instantiated: ArrayBuffer[Boolean],
    remLabelling: (TermRef, SortRef, CtorRefSet))

  // TODO: Consider special case of a single sort with a single constructor,
  //  that is, labels(t) == None -- which then is the implicit representation of
  //  labels(t) == {the single constructor} -- might allow rule Instantiate 2
  //  (and others?).

  protected var sig: Signature = null
  protected var declaredTypes: Typing = null

  protected val stateStack = new mutable.ArrayStack[State]

  // Invariant: size of {terms, eqClass[Siz]es, labels, ...} == nextTermId
  protected var nextTermId: TermRef = 0
  protected var maxVarId: VarId = 0

  protected var terms         = new ArrayBuffer[Term]
  protected var termRefs      = new mutable.HashMap[Term, TermRef]

  protected var eqClasses     = new ArrayBuffer[TermRef]
  protected var eqClassSizes  = new ArrayBuffer[Int]
  protected var eqClassConsts = new ArrayBuffer[Option[ConstId]]
  protected var labels        = new ArrayBuffer[Labels]

  protected var outEdges      = new ArrayBuffer[ArrayBuffer[TermRef]]
  protected var inEdges       = new ArrayBuffer[mutable.HashSet[TermRef]]
  protected var sharedSets    = new mutable.HashMap[(TermRef, TermRef), mutable.HashSet[Index]]

  // selectorsOf maps uninstantiated terms to the set of selectors referring to them
  //  Invariant: outEdges(t).isEmpty || !selectorsOf.contains(t)
  type SelectorMap = mutable.HashMap[(SortRef, CtorRef, Index), Selector]
  protected val emptySelectorMap  = new SelectorMap
  protected var selectorsOf       = new mutable.HashMap[TermRef, SelectorMap]
  // Our notion of inst(antiated) diverges a bit from the paper's:
  // Invariant: instantiated(r) == true iff [ r is the representative of an equivalence class ...
  //  including a Constructor OR the r has just been instantiated and is awaiting merging with ...
  //  the Constructor ]
  protected var instantiated      = new ArrayBuffer[Boolean]

  protected val potentialInst     = new mutable.HashSet[TermRef]
  protected val downSet           = new mutable.ArrayStack[(TermRef, TermRef)]

  var debug = false
  var debug_didSplit = false

  protected def resetState(): Unit = {
    sig = null
    declaredTypes = null

    stateStack.clear()

    // >>> potentially branched part of state
    nextTermId  = 0
    maxVarId    = 0

    terms.clear()
    termRefs.clear()

    eqClasses.clear()
    eqClassSizes.clear()
    eqClassConsts.clear()
    labels.clear()

    outEdges.clear()
    inEdges.clear()
    sharedSets.clear()

    selectorsOf.clear()
    instantiated.clear()
    // <<<

    potentialInst.clear()
    downSet.clear()

    debug_didSplit = false
  }
  
  protected def pushState(remLabelling: (TermRef, SortRef, CtorRefSet)): Unit = {
    // We only push and pop states when closure computation has converged
    assert(downSet.isEmpty)
    assert(potentialInst.isEmpty)

    val _outEdges     = new ArrayBuffer[ArrayBuffer[TermRef]](outEdges.size) ++=
      outEdges.map(_.clone())
    val _inEdges      = new ArrayBuffer[mutable.HashSet[TermRef]](inEdges.size) ++=
      inEdges.map(_.clone())
    val _sharedSets   = new mutable.HashMap[(TermRef, TermRef), mutable.HashSet[Index]] ++=
      sharedSets.mapValues(_.clone())
    val _selectorsOf  = new mutable.HashMap[TermRef, SelectorMap]() ++=
      selectorsOf.mapValues(_.clone())

    val state = State(
      nextTermId, maxVarId,
      terms.clone(), termRefs.clone(),
      eqClasses.clone(), eqClassSizes.clone(), eqClassConsts.clone(), labels.clone(),
      _outEdges, _inEdges, _sharedSets, _selectorsOf, instantiated.clone(),
      remLabelling)
    stateStack push state
  }

  protected def popState(): (TermRef, SortRef, CtorRefSet) = {
    //TODO: Apparently it should be empty, but sometimes it is not, clearing does seem to work
    //assert(downSet.isEmpty)
    //assert(potentialInst.isEmpty)
    downSet.clear()
    potentialInst.clear()

    val state = stateStack.pop()

    nextTermId  = state.nextTermId
    maxVarId    = state.maxVarId

    terms     = state.terms
    termRefs  = state.termRefs

    eqClasses     = state.eqClasses
    eqClassSizes  = state.eqClassSizes
    eqClassConsts = state.eqClassConsts
    labels        = state.labels

    outEdges    = state.outEdges
    inEdges     = state.inEdges
    sharedSets  = state.sharedSets

    selectorsOf   = state.selectorsOf
    instantiated  = state.instantiated

    state.remLabelling
  }


  protected def allTermRefs: Seq[TermRef] = (0 until nextTermId).toSeq

  protected def freshVariable(): Variable = {
    maxVarId += 1
    Variable(maxVarId)
  }

  // Registers a given term and all of its subterms in the solver's internal
  //  data structures. In particular, an id is given to the term -- its
  //  term ref(erence) -- and is returned.
  protected def registerTerm(term: Term): TermRef = {
    if (termRefs contains term)
      return termRefs(term)

    val subTerms    = term.subTerms
    val subTermRefs = subTerms map registerTerm

    val id = nextTermId
    terms             += term
    termRefs(term)    = id
    eqClasses         += id
    eqClassSizes      += 1
    eqClassConsts     += (term match {
      case Constant(constId)  => Some(constId)
      case _                  => None
    })

    labels        += None
    instantiated  += false
    term match {
      case Constructor(sort, ctor, _) =>
        //TODO: rules in the paper don't seem to instantiate there
        instantiated(id) = true // (must be set before label to avoid marking for potentialInst)
        labels(id) = Some((sort, newCtorRefSet(Set(ctor))))
        // FIXME: Should we label our children? (The paper doesn't seem to prescribe this)
      case term@Selector(sort, ctor, index0, arg) =>
        val argSort = sig.argSort(sort, ctor, index0)
        label(id, argSort, sig.ctorRefs(argSort))
        //TODO: selectee is head?
        val selectee = subTermRefs.head
        if (instantiated(selectee)) {
          downSet.push(id, outEdges(selectee)(index0))
        } else {
          selectorsOf.getOrElseUpdate(selectee, new mutable.HashMap) += (sort, ctor, index0) -> term
//          potentialInst add id
        }
      case _ =>
        declaredTypes.get(term) match {
          case Some(sort) =>
            labels(id) = Some((sort, sig.ctorRefs(sort)))
          case None =>
            labels(id) = None // meaning "of any sort and ctor"
        }
    }
    // Is the term's ctor now unambiguous?
    if (!instantiated(id)) {
      labels(id) match {
        case Some((_, ctors)) if ctors.size == 1 =>
          potentialInst add id
        case _ =>
        //
      }
    }
//    printDebug(s"Init ${id} @ ${term} w/ labels ${labels(id)}")

    term match {
      case Variable(varId) if varId > maxVarId => maxVarId = varId
      case _ =>
    }

    val out = new ArrayBuffer[TermRef]()
    outEdges += out
    term match {
      case _: Constructor =>
        out.sizeHint(subTerms.size)
        subTermRefs foreach { subRef =>
          out.append(subRef)
          inEdges(subRef).add(id)
        }
      case _ =>
      // NOTE: We explicitly do not add edges from selector arguments to
      //  selectors here! See instantiation below.
    }
    inEdges += new mutable.HashSet[TermRef]()

    nextTermId += 1
    id
  }

  // Returns the reference (i.e. id) of a term
  protected def ref(term: Term): TermRef =
    termRefs(term)

  // Returns the representative of a term's equivalence class
  protected def repr(ref: TermRef): TermRef = {
    var _ref = ref
    while (eqClasses(_ref) != _ref) {
      eqClasses(_ref) = eqClasses(eqClasses(_ref))
      _ref = eqClasses(_ref)
    }
    _ref
  }

  protected def ctorsOf(ref: TermRef): Seq[(SortRef, CtorRef)] =
    labels(ref) match {
      case None => sig.sorts.zipWithIndex
        .flatMap({ case (ctors, sort) => (0 until ctors.size) map {ctor => (sort, ctor)} }).toSeq
      case Some((sort, ctors)) =>
        ctors.map({ctor => (sort, ctor)}).toSeq
    }

  // The unique ctor of ref, if there is one
  protected def ctorOf(ref: TermRef): Option[(SortRef, CtorRef)] =
    labels(ref) match {
      case None => None
      case Some((_, ctors)) if ctors.size != 1 => None
      case Some((sort, ctors)) => Some((sort, ctors.head))
    }

  // TODO: Instead of recomputing, keep books on HashSet[TermRef] reps
  protected def reps =
    (eqClasses.iterator.zipWithIndex filter {case (s,i) => s == i} map(_._2)).toSeq
//  protected def instantiatedReps =
//    reps filter(instantiated(_))

  protected def sharedSetOf(ri: TermRef, rj: TermRef): mutable.HashSet[Index] = {
    assert(ri != rj)
    val sharedRef = if (ri <= rj) (ri, rj) else (rj, ri)
    sharedSets.getOrElseUpdate(sharedRef, new mutable.HashSet[Index])
  }

  protected def pathExists(from: TermRef, to: TermRef): Boolean = {
    // TODO: Substitute with some efficient data structure + algorithm
    // TODO: Simple optimization: Cache positive queries, as the set of connected pairs
    //  will only increase monotonically (within any given branch).
    val work = new mutable.ArrayStack[TermRef]()
    work.push(from)
    while (work.nonEmpty) {
      val t = repr(work.pop())
      if (t == to)
        return true
      work ++= outEdges(t)
    }
    false
  }

  // Restricts the labelling of term t to the intersection of the previously
  //  known labels of t and the given labels (ctors of the given sort).
  // Returns an UnsatReason if as a result of labelling we detected unsat and
  //  None otherwise.
  protected def label(t: TermRef, sort: SortRef, ctors: CtorRefSet):
      Option[UnsatReason] =
  {
    val rt = repr(t)
    val stillSat = labels(rt) match {
      case None =>
        labels(rt) = Some((sort, ctors))
        ctors.nonEmpty
      case Some((`sort`, ctors0)) =>
        val ctors1 = ctors0 & ctors
        labels(rt) = Some((sort, ctors1))
        ctors1.nonEmpty
      case Some((sort0, _)) => // sort0 != sort
        labels(rt) = Some((sort0, mutable.BitSet.empty))
        false
    }
//    printDebug(s"Labelled ${rt} w/ ${labels(rt)}")

    // Is the term's ctor now unambiguous?
    if (!instantiated(rt)) {
      labels(rt) match {
        case Some((_, ctors1)) if ctors1.size == 1 =>
          potentialInst add rt
        case _ =>
          ()
      }
    }

    // [Selector rules / Collapse 2]
    // TODO: Make this more efficient by grouping elems in the set by ctor?
    labels(rt) match {
      case Some((_, ctors1)) =>
        // Equate all selectors of this term that do not select arguments of one of the
        //  still-feasible constructors with their respective designated term.
        selectorsOf.get(t).map( _
            .collect {case ((_sort, _ctor, _), sel) if _sort != sort || !ctors1.contains(_ctor) => sel}
            .foreach {sel => downSet.push((ref(sel), ref(sig.designatedTerms(sel.sort)(sel.ctor)(sel.index))))}
          )
      case _ =>
        //
    }

    //Check Collapse 2 rule on every term (to make sure, else tests are failing)
    terms.foreach{
      case sel@Selector(sort, ctor, _, term) =>
        val ls = labels(repr(ref(term)))
        ls.foreach{ case (s, ctors) => {
          if(ctors.forall((c: CtorRef) => c != ctor)) {
            downSet.push((ref(sel), ref(sig.designatedTerms(sel.sort)(sel.ctor)(sel.index))))
          }
        }}

      case _ => ()
    }


    if (stillSat) None else Some(EmptyLabelling(rt))
  }

  // Merge equivalence class representative rj *into* rep. ri, i.e. ri will be
  //  the representative of the resulting equivalence class.
  private def _merge(ri: TermRef, rj: TermRef): Either[(TermRef, TermRef), UnsatReason] = {
    printDebug(s"Merging $ri and $rj")
//    printDebug(s"\tBefore: ${labels(ri)} & ${labels(rj)}")

    if (pathExists(ri, rj) || pathExists(rj, ri)) {
      return Right(Cyclic(ri, rj))
    }

    eqClasses(rj) = ri
    eqClassSizes(ri) += eqClassSizes(rj)
    (eqClassConsts(ri), eqClassConsts(rj)) match {
      case (_, None) =>
        // No additional information about representative constants
      case (None, cj) =>
        eqClassConsts(ri) = cj
      case _ =>
        // [Unification closure rules / Clash]
        return Right(Clash(ri, rj))
    }

    labels(rj) match {
      case None =>
      // No additional labelling information
      case Some((sort, ctors)) =>
        val unsatReason = label(ri, sort, ctors)
        if (unsatReason.isDefined)
          return Right(unsatReason.head)
    }
//    printDebug(s"\tAfter: ${labels(ri)}")

    val alreadyInstantiated = instantiated(ri) || instantiated(rj)
    instantiated(ri) = alreadyInstantiated

    // TODO: Optimization: Update shared sets of parents

    inEdges(ri) ++= inEdges(rj)

    val esi = outEdges(ri)
    val esj = outEdges(rj)

    // A term either is already instantiated (and thus has arguments connected to it)
    //  or is uninstantiated and in that case *may* have selectors referring to it.
    assert(esi.isEmpty || !selectorsOf.contains(ri))
    assert(esj.isEmpty || !selectorsOf.contains(rj))

    if (esi.nonEmpty && esj.nonEmpty) {
      assert(alreadyInstantiated)
      assert(esi.size == esj.size)
      downSet ++= esi zip esj

    } else {
      // Potentially merge selectors
      // selectorsOf are implicit (i.e. not yet connected) children that we also need to merge
      (selectorsOf.get(ri), selectorsOf.get(rj)) match {
        // Merge selectors with selectors
        case (Some(selectorsi), Some(selectorsj)) =>
          val keysi = selectorsi.keySet
          val keysj = selectorsj.keySet
          for (key <- keysi intersect keysj)
            downSet push (ref(selectorsi(key)), ref(selectorsj(key)))
          for (key <- keysj diff keysi)
            selectorsi += key -> selectorsj(key)
          // FIXME: Why would we need this? Isn't it covered by label()?
//          if (ctorOf(ri).isDefined)
//            potentialInst add ri

        // Merge selectors with children
        case (Some(selectors), _) if esj.nonEmpty =>
          ctorOf(rj) match { case Some((sort, ctor)) =>
            for (((`sort`, `ctor`, index), sel) <- selectors)
              downSet push (ref(sel), esj(index))
          }
          selectorsOf.remove(ri)
        case (_, Some(selectors)) if esi.nonEmpty =>
          ctorOf(ri) match { case Some((sort, ctor)) =>
            for (((`sort`, `ctor`, index), sel) <- selectors)
              downSet push (ref(sel), esi(index))
          }
          // No need to remove selectors of rj, since ri will be the representative

        case _ =>
          selectorsOf.remove(ri)
      }

      if (esi.isEmpty && esj.nonEmpty)
        esi ++= esj
    }


    Left((ri, rj))
  }

  // Merges the equivalence classes of terms i and j (and additionally does all
  //  sorts of bookkeeping on internal data structures).
  // Returns Some((ri, rj)) if the merge did not violate any constraints, ri is
  //  the equality class' new representative and rj was the (old)
  //  representative of the equality class that was merged into ri's.
  // Returns an UnsatReason if as a result of the merge if we detected unsat.
  protected def merge(i: TermRef, j: TermRef): Either[(TermRef, TermRef), UnsatReason] = {
    val ri = repr(i)
    val rj = repr(j)
    if (ri == rj)
      Left((ri, rj))
    else if (eqClassSizes(rj) <= eqClassSizes(ri))
      _merge(ri, rj)
    else
      _merge(rj, ri)
  }

  // Parts of main loop

  protected def instantiate(): Boolean = {
    var converged = true

    // [Selector rules / Instantiate 1 & 2]
    // TODO: Go through occasions on which potentialInst is populated and perhaps cut them down.
    // A term is added to potentialInst only once, i.e. as soon as a single labels is associated
    //  with it.
    // Terms are never added to potentialInst when they have already been instantiated.
    // However: Due to merges queued up in the downSet, some terms in potentialInst will --
    //  by the time we run this loop -- in fact be in an instantiated equivalence class.
    for (t <- potentialInst if !instantiated(t)) {
//      printDebug(s"Potential instantiation of $t=<${terms(t)}>")
      ctorOf(t) match {
        case Some(sc @ (sort, ctor)) =>
          val shouldInstantiate =
            // Instantiate 1
            (selectorsOf.get(t) match {
              case Some(selectors) =>
                // Basically a combination of rules [Abstract 3] and [Instantiate 1]:
                val indices = sig.argIndices(sort, ctor)
                selectors.keysIterator collect { case (`sort`, `ctor`, i) => i } exists (indices.contains)
              case _ => false
            }) ||
            // Instantiate 2
            sig.isFiniteCtor(sort, ctor)

          if (shouldInstantiate) {
            converged = false
            val selectors = selectorsOf.getOrElse(t, emptySelectorMap)
            var freshVars = Seq[(Index, Variable)]()
            val args = sig.argIndices(sort, ctor) map { index =>
              // FIXME: Should we label the fresh variable with ctors of the argument sort? (relevant for Inst 2)
//              selectors.getOrElse((sort, ctor, index), {freshVariable()})
              selectors.getOrElse((sort, ctor, index), {
                val v = freshVariable()
                freshVars = (index, v) +: freshVars
                v
              })
            }
            val newConstructor = Constructor(sort, ctor, args.toList)
            downSet push (t, registerTerm(newConstructor))
            // Kind of ugly, but we can only do this after registering the term:
            for ((index,v) <- freshVars) {
              val argSort = sig.argSort(sort, ctor, index)
              val unsatReason = label(ref(v), argSort, sig.ctorRefs(argSort))
              assert(unsatReason.isEmpty)
            }
            selectorsOf.remove(t)
            // Implied by merge later on, but we set it here to keep t from being marked
            //  potentialInst again.
            // NOTE: This weakens the semantics of instantiated(_) a bit.
            instantiated(t) = true
            printDebug(s"Instantiated $t=<${niceTerm(t)}> with [$sort $ctor]")
            printDebug(s"\t=> $t=${ref(newConstructor)}=${newConstructor}")
            printDebug(dumpOutEdges())
          }
        case None =>
          assert(false, "Only terms whose ctor has been determined can be instantiated")
      }
    }

    potentialInst.clear()
    converged
  }

  def solve(inst: Instance): Result = {
    // Prepare internal state
    resetState()

    sig = inst.sig
    assert(sig.sorts.size > 0)
    declaredTypes = inst.declaredTypes

    inst.allTopLevelTerms foreach registerTerm
    sig.allDesignatedTerms foreach registerTerm
    printDebug(dumpTerms())

    // Actual algorithm
    // = Process literals

    // [Lit-level rules / Orient]
    inst.eqs foreach { case (s, t) =>
      downSet.push((ref(s), ref(t)))
    }

    // [Lit-level rules / Remove]
    inst.tests foreach {case Tester(sort, ctor, t) =>
      val res = label(ref(t), sort, newCtorRefSet(Set(ctor)))
      if (res.isDefined)
        return Unsat(res.head)
    }

    // TODO: Needs test cases
    // NOTE: Does not exactly match rule 'Remove 2' in the paper
    //  (note difference between sort(v) vs. sort of tester)
    // FIXME: ACTUALLY, neither makes sense.
    inst.negtests foreach {case Tester(sort, ctor, t) =>
      val ctorRefs = sig.ctorRefs(sort) - ctor
      val res = label(ref(t), sort, ctorRefs)
      if (res.isDefined)
        return Unsat(res.head)
    }

    // = Apply 'normal' rules

    // [Congruence closure / Simplify 1, Superpose, Compose]
    //  ... are covered by merge()

    // Alternate between computing unification (downward) and
    //  congruence (upward) closures
    var splittingConverged = false
    var lastUnsatReason: Option[UnsatReason] = None
    while (!splittingConverged) {
      splittingConverged = true
      lastUnsatReason = None

      breakable {
        var closuresConverged = false
        while (!closuresConverged) {
          // Instantiation
          closuresConverged = instantiate()

          // [Unification closure / Decompose]
          while (downSet.nonEmpty) {
            closuresConverged = false
            val (i, j) = downSet.pop()

            merge(i, j) match {
              case Right(unsatReason) =>
                lastUnsatReason = Some(unsatReason)
                downSet.clear()
                break
              case _ =>
              //
            }

          }

          // TODO: Instantiate here as well?

          // [Congruence closure / Simplify 2]
          // TODO: This part is inefficient atm
          // TODO: Don't rebuild repsWithCtors every time?
          val repsInstantiated = reps filter instantiated
          val repsWithDeterminedCtors =
            (repsInstantiated zip (repsInstantiated map ctorOf)
              collect {case (r, Some(sc)) => (r, sc)}).toSeq
          for ((ri, (sorti, ctori)) <- repsWithDeterminedCtors) {
            val esi = outEdges(ri)
            for ((rj, (sortj, ctorj)) <- repsWithDeterminedCtors) {
              if (ri < rj && sorti == sortj && ctori == ctorj) {
                val esj = outEdges(rj)
                val sharedSet = sharedSetOf(ri, rj)
                val indices = sig.argIndices(sorti, ctori).toSet
                for (index <- indices diff sharedSet) {
                  if (repr(esi(index)) == repr(esj(index))) {
                    sharedSet.add(index)
                  }
                }
                //            printDebug(s"sharedSet($ri, $rj) = $sharedSet")
                if (sharedSet.size == indices.size) {
                  closuresConverged = false
                  merge(ri, rj) match {
                    case Right(unsatReason) =>
                      lastUnsatReason = Some(unsatReason)
                      downSet.clear()
                      break
                    case _ =>
                    //
                  }
                }
              }
            }
          }
        } // << while (!converged)
      }

      // = Check inequalities
      // TODO: Check this upon every merge in some efficient way
      inst.ineqs.find {case (s, t) => repr(ref(s)) == repr(ref(t))} match {
        case Some((s,t)) =>
          lastUnsatReason = Some(InvalidEquality(ref(s), ref(t)))
        case _ =>
        //
      }

      // Branching: Here we either
      //  a) continue, because the current branch is unsat and we can still backtrack, OR
      //  b) converge. because we have explored all states and no sat. model was found, OR
      //  c) converge, because a satisfying model has been found, OR
      //  d) continue, because this branch is still undecided (we can still split).
      val wasUnsat = lastUnsatReason.isDefined
      splittingConverged = if (wasUnsat) {
        printDebugIndent(stateStack.size, "branch was unsat")
        // Nothing to split, Unsat branch
        //  i.e. not a model, but we have more states to search
        if (stateStack.nonEmpty) {
          // Pop
          val (r, remSort, remCtors) = popState()
          val unsatReason = label(r, remSort, remCtors)
          assert(unsatReason.isEmpty)
          false // a)
        } else {
          // No more branches to check, ultimately unsat
          true // b)
        }
      } else {
        val splitOn =
          reps find { r =>
            !instantiated(r) && ctorOf(r).isEmpty &&
              ( selectorsOf.contains(r) ||
                ctorsOf(r).forall({case (sort, ctor) => sig.isFiniteCtor(sort, ctor)}) )
          }
        printDebugIndent(stateStack.size, s"split on ${if (splitOn.isEmpty) "nothing" else niceTerm(splitOn.head)}")
        splitOn match {
          case None =>
            // Nothing to split, Sat branch
            //  i.e. we found a model
            true // c)
          case Some(r) =>
            // Split
            debug_didSplit = true
            val (guessedSort, guessedCtor) = labels(r) match {
              case None =>
                printDebug(s"\tsplitting on $r <${niceTerm(r)}>: [universal labeling]")
                val (sort, ctor) = (0, 0)
                // TODO: We should be able to represent arbitrary sets of ctors in labels(),
                //  instead we encode the various remaining sets per sort as a separate return
                //  state per sort.
                for (otherSort <- sig.sortRefs.reverseIterator if otherSort != sort)
                  pushState((r, otherSort, sig.ctorRefs(otherSort)))
                if (sig.sorts(sort).size > 1)
                  pushState((r, sort, sig.ctorRefs(sort) - ctor))
                (sort, ctor)
              case Some((sort, ctors)) =>
                printDebug(s"\tsplitting on $r=<${niceTerm(r)}>: [$sort $ctors]")
                val ctor = ctors.head
                if (ctors.size > 1)
                  pushState((r, sort, ctors - ctor))
                (sort, ctor)
            }
            // Apply guessed labeling
            val unsatReason = label(r, guessedSort, newCtorRefSet(Set(guessedCtor)))
            assert(unsatReason.isEmpty)
            printDebug(s"\tguessed [${guessedSort} ${guessedCtor}]")
            false // d)
        }
      } // << splittingConverged = {true, false}
      printDebug(s"\t(state stack size = ${stateStack.size})")
    } // << while (!splittingConverged)

    printDebug(dumpTerms())
    printDebug(dumpEqClasses())
    printDebug(dumpEqClassLabels())

    // In case we converged via case b) above:
    if (lastUnsatReason.isDefined)
      return Unsat(lastUnsatReason.head)

    // Success!
    val model = {
      val equalSets = new mutable.HashMap[TermRef, mutable.HashSet[TermRef]]
      for (t <- allTermRefs)
        equalSets.getOrElseUpdate(repr(t), new mutable.HashSet()) += t
//      equalSets.values.map(_.map(terms).toSeq).toSeq
      equalSets.map({ case (r,clas) => (ctorOf(r), clas.map(terms).toSeq)  }).toSeq
    }
    Sat(model)
  }


  def dumpTerms(): String =
    (terms.zipWithIndex map { case (term, i) =>
      val strI = i.formatted("%2d")
      s"   $strI: $term"
    }).mkString("Terms:\n", "\n", "")

  def dumpEqClasses(): String = {
    val equalSets = new mutable.HashMap[TermRef, mutable.HashSet[TermRef]]
    for (t <- allTermRefs)
      equalSets.getOrElseUpdate(repr(t), new mutable.HashSet()) += t
    equalSets.map({case (r, set) => s"   $r: $set"}).mkString("Equivalence classes:\n", "\n", "")
  }

  def dumpEqClassLabels(): String = {
    (reps zip (reps map labels))
      .map{ case (r, lbls) => s"   $r: $lbls" }
      .mkString("Equivalence class labels:\n", "\n", "")
  }

  def dumpOutEdges() : String = {
    (reps zip (reps map outEdges))
      .map{ case (r, es) => s"    $r: $es" }
      .mkString("outEdges:\n", "\n", "")
  }

  def debugOn(): Unit = debug = true
  def debugOff(): Unit = debug = false
  def debugDidSplit(): Boolean = debug_didSplit

  protected def printDebug(s: String) =
    if (debug) println(s)
  protected def printDebugIndent(depth: Int, s: String, indentStr: String = "+") =
    if (debug) println("<" + indentStr*depth + " " + s)

  protected def HEY() = {
    printDebug((new IllegalArgumentException).getStackTrace().mkString("HEY:\n","\n","\n"))
  }

  def termNiceness(term: Term): Int = term match {
    case _: Variable => 0
    case _: Constant => 2
    case _: Selector => 1
    case _: Constructor => 3
  }
  protected def niceTerm(r: TermRef) =
    terms(allTermRefs filter(repr(_) == r) maxBy({t => termNiceness(terms(t))}))
}
