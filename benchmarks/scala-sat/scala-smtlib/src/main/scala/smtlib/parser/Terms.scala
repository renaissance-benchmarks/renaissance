package smtlib
package parser

import common._


/*
 * =========== IMPORTANT ================
 * This file is still work in progress, the hierarchy is not yet used in the library,
 * but is expected to replace the s-expr based interface at some point.
 *
 * Even though it is a bit annoying to have a layer on top of the S-expression syntax;
 * it seems reasonable to have a well typed SMT-LIB tree to interact with the parser/printer.
 *
 * That choice is also influenced by the somewhat unclear treatment of upper/lower case symbols in SMT-LIB.
 */

import Commands._

object Terms {

  //an identifier is either a symbol or an indexed symbol: (_ symbol <numeral>+)
  trait Identifier {
    val symbol: SSymbol
    val indices: Seq[Int]

    def isIndexed: Boolean = !indices.isEmpty
  }
  //provide apply/unapply for standard Identifier
  object Identifier {
    def apply(symbol: SSymbol, indices: Seq[Int] = Seq()): Identifier = 
      StandardIdentifier(symbol, indices)

    def unapply(id: Identifier): Option[(SSymbol, Seq[Int])] = id match {
      case StandardIdentifier(s, is) => Some((s, is))
      case _ => None
    }
  }

  case class StandardIdentifier(symbol: SSymbol, indices: Seq[Int]) extends Identifier
  //non standard, example:  (_ map or)
  case class ExtendedIdentifier(symbol: SSymbol, extension: SSymbol) extends Identifier {
    val indices: Seq[Int] = Seq()
  }

  case class Sort(id: Identifier, subSorts: Seq[Sort]) {
    override def toString: String = printer.PrettyPrinter.toString(this)
  }
  object Sort {
    def apply(id: Identifier): Sort = Sort(id, Seq())
  }

  case class Attribute(keyword: SKeyword, v: Option[SExpr])
  object Attribute {
    def apply(key: SKeyword): Attribute = Attribute(key, None)
  }

  case class SortedVar(name: SSymbol, sort: Sort)
  case class VarBinding(name: SSymbol, term: Term)


  trait SExpr extends Positioned

  case class SList(sexprs: List[SExpr]) extends SExpr
  object SList {
    def apply(sexprs: SExpr*): SList = SList(List(sexprs:_*))
  }
  case class SKeyword(name: String) extends SExpr
  case class SSymbol(name: String) extends SExpr

  /* SComment is never parsed, only used for pretty printing */
  case class SComment(s: String) extends SExpr 

  sealed abstract class Term extends Positioned with SExpr {
    override def toString: String = printer.PrettyPrinter.toString(this)
  }

  case class Let(binding: VarBinding, bindings: Seq[VarBinding], term: Term) extends Term
  case class ForAll(sortedVar: SortedVar, sortedVars: Seq[SortedVar], term: Term) extends Term
  case class Exists(sortedVar: SortedVar, sortedVars: Seq[SortedVar], term: Term) extends Term

  case class QualifiedIdentifier(id: Identifier, sort: Option[Sort]) extends Term
  object QualifiedIdentifier {
    def apply(id: Identifier): QualifiedIdentifier = QualifiedIdentifier(id, None)
  }

  case class AnnotatedTerm(term: Term, attribute: Attribute, attributes: Seq[Attribute]) extends Term
  case class FunctionApplication(fun: QualifiedIdentifier, terms: Seq[Term]) extends Term //TODO: should terms be at leat of length 1 ?

  trait Constant extends Term

  trait Literal[T] extends Constant {
    val value: T
  }

  case class SNumeral(value: BigInt) extends Literal[BigInt]
  case class SHexadecimal(value: Hexadecimal) extends Literal[Hexadecimal]
  case class SBinary(value: List[Boolean]) extends Literal[List[Boolean]]
  case class SDecimal(value: BigDecimal) extends Literal[BigDecimal]
  case class SString(value: String) extends Literal[String]

}
