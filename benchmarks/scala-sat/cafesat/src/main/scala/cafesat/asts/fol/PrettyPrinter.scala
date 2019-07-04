package cafesat.asts
package fol

import fol.Trees._
import core.Trees.{Formula, Term}

object PrettyPrinter {

  val ANDSTR = " \u2227 "
  val ORSTR  = " \u2228 "
  val NOTSTR = "\u00AC"
  val IMPLIESSTR = " \u2192 "
  val IFFSTR = " \u2194 "
  val TRUESTR  = "\u22A4"
  val FALSESTR = "\u22A5"
  val EQSTR = " = "
  val NESTR  = " \u2260 "

  def apply(formula: Formula): String = formulaPrinter(formula, _ => None, _ => None)
  def apply(term: Term): String = termPrinter(term, _ => None, _ => None)

  def formulaPrinter(formula: Formula, dfp: (Formula) => Option[String], dtp: (Term) => Option[String]): String = {
    def fdfp(f: Formula): Option[String] = dfp(f) match {
      case o@Some(s) => o
      case None => defaultFormulaPrinter(f, dfp, dtp)
    }
    core.PrettyPrinter.formulaPrinter(formula, fdfp, dtp)
  }
  def termPrinter(term: Term, dfp: (Formula) => Option[String], dtp: (Term) => Option[String]): String = {
    def fdfp(f: Formula): Option[String] = dfp(f) match {
      case o@Some(s) => o
      case None => defaultFormulaPrinter(f, dfp, dtp)
    }
    core.PrettyPrinter.termPrinter(term, fdfp, dtp)
  }

  private def defaultFormulaPrinter(formula: Formula, dfp: (Formula) => Option[String], dtp: (Term) => Option[String]): Option[String] = formula match {
    case And(fs) => Some(fs.map(f => formulaPrinter(f, dfp, dtp)).mkString("(", ANDSTR, ")"))
    case Or(fs)  => Some(fs.map(f => formulaPrinter(f, dfp, dtp)).mkString("(", ORSTR, ")"))
    case Not(f)  => Some(NOTSTR + formulaPrinter(f, dfp, dtp)) 
    case Implies(f1, f2) => Some("(" + formulaPrinter(f1, dfp, dtp) + IMPLIESSTR + formulaPrinter(f2, dfp, dtp) + ")")
    case Iff(f1, f2) => Some("(" + formulaPrinter(f1, dfp, dtp) + IFFSTR + formulaPrinter(f2, dfp, dtp) + ")")
    case True()  => Some(TRUESTR)
    case False() => Some(FALSESTR)
    case Equals(t1, t2) => Some("(" + termPrinter(t1, dfp, dtp) + EQSTR + termPrinter(t2, dfp, dtp) + ")")
    case _ => None
  }
}
