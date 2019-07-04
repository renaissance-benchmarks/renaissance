package cafesat
package api

import Formulas._

import asts.fol

/** Provides extractors to manipulate [[Formulas.Formula]] */
object Extractors {

  object Or {
    def unapply(f: Formula): Option[(Formula, Formula)] = f.formula match {
      case fol.Trees.Or(f1 :: f2 :: Nil) => Some((new Formula(f1), new Formula(f2)))
      case fol.Trees.Or(f1 :: f2 :: fs) => Some((new Formula(f1), new Formula(fol.Trees.Or(f2::fs))))
      case _ => None
    }
  }

  object And {
    def unapply(f: Formula): Option[(Formula, Formula)] = f.formula match {
      case fol.Trees.And(f1 :: f2 :: Nil) => Some((new Formula(f1), new Formula(f2)))
      case fol.Trees.And(f1 :: f2 :: fs) => Some((new Formula(f1), new Formula(fol.Trees.And(f2::fs))))
      case _ => None
    }
  }

  object Not {
    def unapply(f: Formula): Option[Formula] = f.formula match {
      case fol.Trees.Not(f) => Some(new Formula(f))
      case _ => None
    }
  }

}
