package smtlib
package theories

import trees.Terms._

import Operations._

object Ints {

  object IntSort {
    def apply(): Sort = {
      Sort(Identifier(SSymbol("Int")))
    }
    def unapply(sort: Sort): Boolean = sort match {
      case Sort(Identifier(SSymbol("Int"), Seq()), Seq()) => true
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

  object Divisible {
    def apply(n: BigInt, t: Term): Term =
      FunctionApplication(
        QualifiedIdentifier(Identifier(SSymbol("divisible"), Seq(SNumeral(n)))),
        Seq(t)
      )
    def unapply(term: Term): Option[(BigInt, Term)] = term match {
      case FunctionApplication(
        QualifiedIdentifier(
          Identifier(SSymbol("divisible"), Seq(SNumeral(n))),
          None
        ), Seq(t)) => Some((n, t))
      case _ => None
    }
  }

  object Neg extends Operation1 { override val name = "-" }
  object Add extends Operation2 { override val name = "+" }
  object Sub extends Operation2 { override val name = "-" }
  object Mul extends Operation2 { override val name = "*" }
  object Div extends Operation2 { override val name = "div" }
  object Mod extends Operation2 { override val name = "mod" }
  object Abs extends Operation1 { override val name = "abs" }

  object LessThan extends Operation2 { override val name = "<" }
  object LessEquals extends Operation2 { override val name = "<=" }
  object GreaterThan extends Operation2 { override val name = ">" }
  object GreaterEquals extends Operation2 { override val name = ">=" }

}
