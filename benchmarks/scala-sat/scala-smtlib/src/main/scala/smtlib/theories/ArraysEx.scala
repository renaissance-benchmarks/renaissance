package smtlib
package theories

import trees.Terms._

import Operations._

object ArraysEx {

  object ArraySort {
    def apply(from: Sort, to: Sort): Sort = Sort(Identifier(SSymbol("Array")), Seq(from, to))
    def unapply(sort: Sort): Option[(Sort, Sort)] = sort match {
      case Sort(Identifier(SSymbol("Array"), Seq()), Seq(from, to)) => Some((from, to))
      case _ => None
    }
  }

  object Select extends Operation2 { override val name = "select" }
  object Store extends Operation3 { override val name = "store" }

}
