package smtlib
package parser

import lexer.Tokens
import Parser._
import trees.Terms._
import common.Position

import scala.collection.mutable.ListBuffer

trait ParserTerms { this: ParserCommon =>

  private def parseQualifiedIdentifier: QualifiedIdentifier = {
    getPeekToken.kind match {
      case Tokens.OParen => {
        val pos = getPeekToken.getPos
        eat(Tokens.OParen)
        val res = getPeekToken.kind match {
          case Tokens.As => {
            parseAsIdentifier.setPos(pos)
          }
          case Tokens.Underscore => {
            QualifiedIdentifier(parseUnderscoreIdentifier.setPos(pos)).setPos(pos)
          }
          case _ => expected(peekToken, Tokens.As, Tokens.Underscore)
        }
        eat(Tokens.CParen)
        res
      }
      case _ => {
        val id = parseIdentifier
        QualifiedIdentifier(id).setPos(id)
      }
    }
  }

  protected def parseTermWithoutParens(startPos: Position): Term = getPeekToken.kind match {
    case Tokens.Let =>
      eat(Tokens.Let)
      val (head, bindings) = parseOneOrMore(() => parseVarBinding)
      val term = parseTerm
      Let(head, bindings, term)

    case Tokens.Forall =>
      eat(Tokens.Forall)
      val (head, vars) = parseOneOrMore(() => parseSortedVar)
      val term = parseTerm
      Forall(head, vars, term)

    case Tokens.Exists =>
      eat(Tokens.Exists)
      val (head, vars) = parseOneOrMore(() => parseSortedVar)
      val term = parseTerm
      Exists(head, vars, term)

    case Tokens.ExclamationMark =>
      eat(Tokens.ExclamationMark)
      val term = parseTerm
      val head = parseAttribute
      val attrs = parseUntil(Tokens.CParen, eatEnd = false)(() => parseAttribute)
      AnnotatedTerm(term, head, attrs)

    case Tokens.As =>
      parseAsIdentifier

    case Tokens.Underscore =>
      QualifiedIdentifier(parseUnderscoreIdentifier.setPos(startPos)).setPos(startPos)

    case _ => //should be function application
      val id = parseQualifiedIdentifier 
      val head = parseTerm
      val terms = parseUntil(Tokens.CParen, eatEnd = false)(() => parseTerm)
      FunctionApplication(id, head::terms.toList)
  }

  def parseTerm: Term = {
    if(getPeekToken.kind == Tokens.OParen) {
      val startPos = getPeekToken.getPos
      val t = parseWithin(Tokens.OParen, Tokens.CParen)(() => parseTermWithoutParens(startPos))
      t.setPos(startPos)
    } else {
      val cst = tryParseConstant
      cst.getOrElse({
        val id = parseIdentifier
        QualifiedIdentifier(id).setPos(id)
      })
    }
  }


  def tryParseConstant: Option[Constant] = {
    getPeekToken.kind match {
      case Tokens.NumeralLitKind => Some(parseNumeral)
      case Tokens.HexadecimalLitKind => Some(parseHexadecimal)
      case Tokens.BinaryLitKind => Some(parseBinary)
      case Tokens.DecimalLitKind => Some(parseDecimal)
      case Tokens.StringLitKind => Some(parseString)
      case _ => None
    }
  }


  def parseVarBinding: VarBinding = {
    val start = eat(Tokens.OParen)
    val sym = parseSymbol
    val term = parseTerm
    eat(Tokens.CParen)
    VarBinding(sym, term).setPos(start)
  }
  def parseSortedVar: SortedVar = {
    val start = eat(Tokens.OParen)
    val sym = parseSymbol
    val sort = parseSort
    eat(Tokens.CParen)
    SortedVar(sym, sort).setPos(start)
  }

}
