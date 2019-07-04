package cafesat.sat

import scala.collection.mutable.HashMap
import scala.collection.mutable.HashSet
import scala.collection.mutable.Stack
import scala.collection.mutable.ArrayBuffer

object ProofPrinter {

  def toDot(inferences: Array[Inference]): String = {
    
    def nodeId(id: Int): String = "v" + id

    val infToIndex = inferences.zipWithIndex.toMap
    val vertexLabels: Seq[String] = infToIndex.map(p => 
      nodeId(p._2) + " [label=\"" + p._1.clause.mkString(", ") + "\"];").toSeq

    val edges: Seq[String] = infToIndex.flatMap{
      case (ResolutionInference(cl, left, right), i) => List(
        nodeId(infToIndex(left)) + " -> " + nodeId(i) + ";",
        nodeId(infToIndex(right)) + " -> " + nodeId(i) + ";")
      case (_, _) => List()
    }.toSeq

    "digraph proof {\n" +
      vertexLabels.mkString("  ", "\n  ", "\n") +
      edges.mkString("  ", "\n  ", "\n") + "}"
  }

  def toString(inferences: Array[Inference]): String = {
    val infToIndex = inferences.zipWithIndex.toMap
    
    inferences.zipWithIndex.map{
      case (InputInference(cl), i) => 
        "[" + i + "] " + 
        cl.mkString(", ") +
        " INPUT"
      case (ResolutionInference(cl, left, right), i) =>
        "[" + i + "] " + 
        cl.mkString(", ") +
        " RESOL {" + infToIndex(left) + ", " + infToIndex(right) + "}"
    }.mkString("\n")
  }

}
