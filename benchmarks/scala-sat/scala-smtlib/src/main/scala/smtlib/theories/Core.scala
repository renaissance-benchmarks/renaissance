package smtlib
package theories

import trees.Terms._

import Operations._

object Core {

  object BoolSort {
    def apply(): Sort = Sort(Identifier(SSymbol("Bool")))
    def unapply(sort: Sort): Boolean = sort match {
      case Sort(Identifier(SSymbol("Bool"), Seq()), Seq()) => true
      case _ => false
    }
  }

  object BoolConst {
    def apply(v: Boolean): Term = if(v) True() else False()
  }

  object True extends Operation0 { override val name = "true" }
  object False extends Operation0 { override val name = "false" }

  object Not extends Operation1 { override val name = "not" }
  object Implies extends Operation2 { override val name = "=>" }
  object And extends OperationN2 { override val name = "and" }
  object Or extends OperationN2 { override val name = "or" }
  object Xor extends Operation2 { override val name = "xor" }

  object Equals extends Operation2 { override val name = "=" }

  object ITE extends Operation3 { override val name = "ite" }

}
