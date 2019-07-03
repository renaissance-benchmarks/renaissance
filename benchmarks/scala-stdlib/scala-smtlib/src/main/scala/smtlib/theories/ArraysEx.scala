package smtlib
package theories

import parser.Terms._

object ArraysEx {


  object ArraySort {

    def apply(from: Sort, to: Sort): Sort = Sort(Identifier(SSymbol("Array")), Seq(from, to))

    def unapply(sort: Sort): Option[(Sort, Sort)] = sort match {
      case Sort(Identifier(SSymbol("Array"), Seq()), Seq(from, to)) => Some((from, to))
      case _ => None
    }

  }

  object Select {
    
    def apply(array: Term, index: Term): Term = 
      FunctionApplication(QualifiedIdentifier(Identifier(SSymbol("select"))), Seq(array, index))

    def unapply(term: Term): Option[(Term, Term)] = term match {
      case FunctionApplication(
        QualifiedIdentifier(
          Identifier(SSymbol("select"), Seq()),
          None
        ), Seq(array, index)) => Some((array, index))
      case _ => None
    }

  }

  object Store {
    
    def apply(array: Term, index: Term, value: Term): Term = 
      FunctionApplication(QualifiedIdentifier(Identifier(SSymbol("store"))), Seq(array, index, value))

    def unapply(term: Term): Option[(Term, Term, Term)] = term match {
      case FunctionApplication(
        QualifiedIdentifier(
          Identifier(SSymbol("term"), Seq()),
          None
        ), Seq(array, index, value)) => Some((array, index, value))
      case _ => None
    }

  }

}
