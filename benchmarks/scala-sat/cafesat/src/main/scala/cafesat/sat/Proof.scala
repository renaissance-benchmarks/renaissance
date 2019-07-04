package cafesat.sat

import scala.collection.mutable.HashMap
import scala.collection.mutable.HashSet
import scala.collection.mutable.Stack
import scala.collection.mutable.ArrayBuffer

/*
 * This objects follows an imperative style.
 * It is first initialized with the set of input clauses.
 * Then inference are added one by one with a call to infer, for this
 * step we should only reference to previously added inferences.
 * Finally, when the proof is completed, it needs to be linearized
 * with the conclusion that one wishes to prove (usually a contradiction 
 * in the form of the empty clause).
 * Once linearized, the proof becomes immutable so only getter can
 * be invoked on it.
 */
class Proof(inputs: Set[Set[Literal]]) {

  private var inferencesOpt: Option[Array[Inference]] = None

  def isFinalized: Boolean = inferencesOpt != None

  def inferences: Array[Inference] = {
    require(inferencesOpt != None)
    inferencesOpt.get
  }

  private val literalsToInferences: HashMap[Set[Literal], Inference] = new HashMap()
  literalsToInferences ++= inputs.map(clause => (clause, new InputInference(clause)))

  //this builds a resolution inference without any check
  //we assume that a separate proof checker has the duty to make sure
  //each inference is correct.
  //This code ensures that the inferences are already present in
  //the proof and make sure to reuse existing node as much as possible
  def infer(left: Set[Literal], right: Set[Literal], concl: Set[Literal]) {
    require(inferencesOpt == None)
    literalsToInferences.get(concl) match {
      case Some(_) =>
      case None =>
        val leftInf = literalsToInferences(left)
        val rightInf = literalsToInferences(right)
        val inf = new ResolutionInference(concl, leftInf, rightInf)
        literalsToInferences(concl) = inf
    }
  }

  /*
   * This method should be called in the end, when all inferences
   * have been added and the proof finalized.
   * This produces a compact array of ordored inferences, where
   * each premise of an inference is found earlier in the array.
   */
  def linearize(conclusion: Set[Literal]) {
    require(inferencesOpt == None) 
    var buffer: ArrayBuffer[Inference] = new ArrayBuffer
    var inferencesAdded = new HashSet[Inference]
    var stack: Stack[Inference] = new Stack()
    stack.push(literalsToInferences(conclusion))
    while(!stack.isEmpty) {
      val inf = stack.top
      if(inferencesAdded.contains(inf))
        stack.pop
      else inf match {
        case InputInference(_) =>
          stack.pop
          buffer.append(inf)
          inferencesAdded += inf
        case ResolutionInference(_, left, right) =>
          if(inferencesAdded.contains(left) && inferencesAdded.contains(right)) {
            stack.pop
            buffer.append(inf)
            inferencesAdded += inf
          } else {
            stack.push(left)
            stack.push(right)
          }
      }
    }
    inferencesOpt = Some(buffer.toArray)
  }

}
