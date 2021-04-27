package smtlib
package theories

import trees.Terms._

import Operations._

object Reals {

  /*
   * TODO: how about providing a Rational constructor? maybe it should go in Constructors?
   */

  object RealSort {
    def apply(): Sort = {
      Sort(Identifier(SSymbol("Real")))
    }
    def unapply(sort: Sort): Boolean = sort match {
      case Sort(Identifier(SSymbol("Real"), Seq()), Seq()) => true
      case _ => false
    }
  }

  object NumeralLit {
    def apply(value: BigInt): Term = SNumeral(value)
    def unapply(term: Term): Option[BigInt] = term match {
      case SNumeral(value) => Some(value)
      case _ => None
    }
  }
  
  object DecimalLit {
    def apply(value: BigDecimal): Term = SDecimal(value)
    def unapply(term: Term): Option[BigDecimal] = term match {
      case SDecimal(value) => Some(value)
      case _ => None
    }
  }

  object Neg extends Operation1 { override val name = "-" }
  object Add extends Operation2 { override val name = "+" }
  object Sub extends Operation2 { override val name = "-" }
  object Mul extends Operation2 { override val name = "*" }
  object Div extends Operation2 { override val name = "/" }

  object LessThan extends Operation2 { override val name = "<" }
  object LessEquals extends Operation2 { override val name = "<=" }
  object GreaterThan extends Operation2 { override val name = ">" }
  object GreaterEquals extends Operation2 { override val name = ">=" }

}
