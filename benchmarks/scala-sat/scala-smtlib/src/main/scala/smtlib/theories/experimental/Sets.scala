package smtlib
package theories
package experimental

import trees.Terms._
import Operations._

/* Experimental support for the theory of sets in CVC4
 * Based on the operations in http://cvc4.cs.nyu.edu/wiki/Sets
 */
object Sets {

  private val SetUnion: String = "union"
  private val SetIntersection: String = "intersection"
  private val SetMinus: String = "setminus"
  private val SetMember: String = "member"
  private val SetSubset: String = "subset"
  private val SetEmptyset: String = "emptyset"
  private val SetSingleton: String = "singleton"
  private val SetInsert: String = "insert"
  private val SetCard: String = "card"

  object SetSort {
    def apply(el : Sort): Sort = Sort(Identifier(SSymbol("Set")), Seq(el))

    def unapply(sort : Sort): Option[Sort] = sort match {
      case Sort(Identifier(SSymbol("Set"), Seq()), Seq(el)) => Some(el)
      case _ => None
    }
  }

  object Union extends Operation2 { override val name = SetUnion }
  object Intersection extends Operation2 { override val name = SetIntersection }
  object Setminus extends Operation2 { override val name = SetMinus }
  object Member extends Operation2 { override val name = SetMember }
  object Subset extends Operation2 { override val name = SetSubset }

  object EmptySet {
    def apply(s : Sort): Term = QualifiedIdentifier(Identifier(SSymbol(SetEmptyset)), Some(s))
    def unapply(t : Term): Option[Sort] = t match {
      case QualifiedIdentifier(Identifier(SSymbol(SetEmptyset), Seq()), Some(s)) =>
          Some(s)
      case _ => None
    }
  }

  object Singleton extends Operation1 { override val name = SetSingleton }

  object Insert extends OperationN2 { override val name = SetInsert }

  object Card extends Operation1 { override val name = SetCard }
}
