package cafesat.sat

import scala.collection.mutable.HashMap

object ProofChecker {

  def apply(inferences: Array[Inference], fact: Set[Literal]): Boolean = {
    val lastInference = inferences.last

    if(lastInference.clause != fact) false else {

      val infToIndex = new HashMap[Inference, Int]

      var i = 0
      var isValid = true

      //make sure that every resolution step is valid
      while(i < inferences.size && isValid) {
        try {
          inferences(i) match {
            case inf@InputInference(_) => //input clause is valid
              infToIndex(inf) = i
            case inf@ResolutionInference(cl, left, right) => {
              val leftIndex = infToIndex(left)
              val rightIndex = infToIndex(right)
              if(leftIndex >= i || rightIndex >= i) //only refer to previous inferences
                isValid = false
              else if(!isResolvent(cl, left.clause, right.clause)) {
                println("INVALID INFERENCE !")
                println("\tleft premise: " + left.clause)
                println("\tright premise: " + right.clause)
                println("\t => " + cl)
                isValid = false
              } else
                infToIndex(inf) = i
            }
          }
        } catch {
          case (_: Throwable) => isValid = false
        }
        i += 1
      }
      isValid
    }
  }

  def isResolvent(resolvent: Set[Literal], left: Set[Literal], right: Set[Literal]): Boolean = {
    left.exists(l1 => right.exists(l2 =>
      l1.getID == l2.getID && l1.polarity != l2.polarity && 
      resolvent == (left.filterNot(_ == l1) ++ right.filterNot(_ == l2))
    ))
  }

}


/*
 * From tree of proof get a graph of proof
 */
  //val inferences: Array[Inference] = {

  //  var inf2index: HashMap[Inference, Int] = new HashMap()
  //  var buffer: ArrayBuffer[Inference] = new ArrayBuffer()
  //  var i = 0
  //  var queue: Queue[Inference] = new Queue()
  //  queue.enqueue(contradiction)

  //  while(!queue.isEmpty) {
  //    val current = queue.dequeue

  //    if(!inf2index.contains(current)) {
  //      current match {
  //        case InputInference(cl) =>
  //          val newInf = RefInputInference(i, cl)
  //          inf2index(current) = i
  //          i += 1
  //          buffer.append(newInf)
  //        case ResolutionInference(cl, left, right) =>
  //          (inf2index.get(left), inf2index.get(right)) match {
  //            case (None, None) =>
  //              queue.enqueue(left)
  //              queue.enqueue(right)
  //              queue.enqueue(current)
  //            case (None, _) => 
  //              queue.enqueue(left)
  //              queue.enqueue(current)
  //            case (_, None) => 
  //              queue.enqueue(right)
  //              queue.enqueue(current)
  //            case (Some(il), Some(ir)) =>
  //              val newInf = RefResolutionInference(i, cl, il, ir)
  //              inf2index(current) = i
  //              i += 1
  //              buffer.append(newInf)
  //          }
  //        case _ => sys.error("unexpected")
  //      }
  //    }
  //  }

  //  buffer.toArray
  //}

