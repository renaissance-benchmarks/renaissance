package cafesat.sat

//equality is only defined by references on Inference, no deep equality
abstract class Inference {
  val clause: Set[Literal]
}

class ResolutionInference(val clause: Set[Literal], val leftPremise: Inference, val rightPremise: Inference) extends Inference {

  override def toString: String = {
    leftPremise.clause.toString + " AND " + rightPremise.clause.toString + " => " + clause.toString
  }
}

object ResolutionInference {

  def unapply(inf: ResolutionInference) =
    if(inf == null) None else Some((inf.clause, inf.leftPremise, inf.rightPremise))

}

class InputInference(val clause: Set[Literal]) extends Inference {
  override def toString: String = {
    clause.toString
  }
}

object InputInference {

  def unapply(inf: InputInference): Option[Set[Literal]] =
    if(inf == null) None else Some(inf.clause)

}
