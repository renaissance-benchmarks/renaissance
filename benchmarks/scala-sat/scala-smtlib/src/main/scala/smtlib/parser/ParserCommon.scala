package smtlib
package parser

import lexer.Tokens
import Tokens.{Token, TokenKind}
import lexer.Lexer
import trees.Terms._

import scala.collection.mutable.ListBuffer

/*
 * ParserCommon exports common feature of the parser. That
 * is, the useful functions to apply parsing (parseMany, parseUntil, etc)
 * as well as the core Lexer + lookahead mecanism. It also provides basic
 * syntactic units that don't really belong to Terms or Commands, such as
 * attributes and identifiers.
 */
trait ParserCommon {
  
  val lexer: Lexer

  import Parser._

  private var _currentToken: Token = null
  /* lookAhead token is Some(null) if we reached eof */
  private var _lookAhead: Option[Token] = None

  //return a next token or throw UnexpectedEOFException if the next token is null
  protected def nextToken(): Token = {
    _lookAhead match {
      case Some(t) => {
        _lookAhead = None
        _currentToken = t
        t
      }
      case None => {
        _currentToken = lexer.nextToken
        _lookAhead = None
        _currentToken
      }
    }
  }

  /*
   * return the look ahead token, or null if EOF
   * Note: do not throw an exception as it is okay to lookahead into EOF
   */
  protected def peekToken: Token = {
    _lookAhead match {
      case Some(t) => t
      case None => {
        _lookAhead = Some(lexer.nextToken)
        _lookAhead.get
      }
    }
  }

  /*
   * Same as peekToken, but expect a token to be present
   * and result in a UnexpectedEOFException if the token is null
   */
  protected def getPeekToken: Token = {
    val tmp = peekToken
    if(tmp == null)
      throw new UnexpectedEOFException(Seq())
    tmp
  }

  /*
   * Make sure the next token has the expected kind and read it
   */
  protected def eat(expected: TokenKind): Token = {
    val token = nextToken()
    check(token, expected)
    token
  }
  /*
   * Make sure the next token is exactly ``expected`` (usually a symbol lit)
   */
  protected def eat(expected: Token): Token = {
    val token = nextToken()
    if(token != expected)
      throw new UnexpectedTokenException(token, Seq(expected.kind))
    token
  }


  protected def check(current: Token, exp: TokenKind): Unit = {
    if(current == null)
      throw new UnexpectedEOFException(Seq(exp))

    if(current.kind != exp) {
      expected(current, exp)
    }
  }

  protected def parseBefore[A](endKind: TokenKind)(parseFun: () => A): A = {
    val res = parseFun()
    eat(endKind)
    res
  }

  protected def parseWithin[A](startKind: TokenKind, endKind: TokenKind)(parseFun: () => A): A = {
    eat(startKind)
    parseBefore(endKind)(parseFun)
  }

  protected def parseUntil[A](endKind: TokenKind, eatEnd: Boolean = true)(parseFun: () => A): Seq[A] = {
    val items = new ListBuffer[A]
    while(peekToken != null && peekToken.kind != endKind)
      items.append(parseFun())

    if(eatEnd)
      eat(endKind)

    items.toList
  }

  protected def parseMany[A](parseFun: () => A): Seq[A] = {
    eat(Tokens.OParen)
    parseUntil(Tokens.CParen)(parseFun)
  }

  /* Parse a sequence of A inside () */
  protected def parseOneOrMore[A](parseFun: () => A): (A, Seq[A]) = {
    val items = new ListBuffer[A]
    eat(Tokens.OParen)
    val head = parseFun()
    while(peekToken != null && peekToken.kind != Tokens.CParen)
      items.append(parseFun())
    eat(Tokens.CParen)
    (head, items.toList)
  }

  //TODO: we need a token class/type, instead of precise token with content + position
  protected def expected(found: Token, expected: TokenKind*): Nothing = {
    if(found == null)
      throw new UnexpectedEOFException(expected)
    else
      throw new UnexpectedTokenException(found, expected)
  }


  /*
   * From now on, parse methods for shared syntactic units
   */

  def parseAttribute: Attribute = {
    val keyword = parseKeyword
    val attributeValue = tryParseAttributeValue
    Attribute(keyword, attributeValue).setPos(keyword)
  }

  def parseAttributeValue: AttributeValue = {
    val attributeValuesTokenKinds: Seq[Tokens.TokenKind] = Seq(
      Tokens.NumeralLitKind, Tokens.BinaryLitKind, Tokens.HexadecimalLitKind, 
      Tokens.DecimalLitKind, Tokens.StringLitKind, Tokens.SymbolLitKind, Tokens.OParen)
    getPeekToken.kind match {
      case Tokens.NumeralLitKind => parseNumeral
      case Tokens.BinaryLitKind => parseBinary
      case Tokens.HexadecimalLitKind => parseHexadecimal
      case Tokens.DecimalLitKind => parseDecimal
      case Tokens.StringLitKind => parseString
      case Tokens.SymbolLitKind => parseSymbol
      case Tokens.OParen => parseSList
      case _ => expected(peekToken, attributeValuesTokenKinds:_*)
    }
  }
  def tryParseAttributeValue: Option[AttributeValue] = {
    if(peekToken == null) None else peekToken.kind match {
      case Tokens.NumeralLitKind => Some(parseNumeral)
      case Tokens.BinaryLitKind => Some(parseBinary)
      case Tokens.HexadecimalLitKind => Some(parseHexadecimal)
      case Tokens.DecimalLitKind => Some(parseDecimal)
      case Tokens.StringLitKind => Some(parseString)
      case Tokens.SymbolLitKind => Some(parseSymbol)
      case Tokens.OParen => Some(parseSList)
      case _ => None
    }
  }


  def parseKeyword: SKeyword = {
    nextToken() match {
      case t@Tokens.Keyword(k) => {
        val keyword = SKeyword(k)
        keyword.setPos(t)
      }
      case token => expected(token, Tokens.KeywordKind)
    }
  }

  def parseSort: Sort = {
    if(getPeekToken.kind == Tokens.OParen) {
      val startPos = getPeekToken.getPos
      eat(Tokens.OParen)

      val res = if(getPeekToken.kind == Tokens.Underscore) {
        val qid = parseUnderscoreIdentifier.setPos(startPos)
        Sort(qid).setPos(startPos)
      } else {
        val name = parseIdentifier

        val subSorts = parseUntil(Tokens.CParen, eatEnd = false)(() => parseSort)

        Sort(name, subSorts.toList).setPos(startPos)
      }
      eat(Tokens.CParen)
      res
    } else {
      val id = parseIdentifier
      Sort(id).setPos(id)
    }
  }

  //currently not used, but should be used with identifiers
  //however we parse any s-expr as an index currently for
  //convenience reason with existing tools (not correct standard-wise)
  def parseIndex: Index = {
    getPeekToken.kind match {
      case Tokens.SymbolLitKind => parseSymbol
      case Tokens.NumeralLitKind => parseNumeral
      case _ => expected(peekToken, Tokens.SymbolLitKind, Tokens.NumeralLitKind)
    }
  }

  //the caller should set the position of the id to be the OParen
  def parseUnderscoreIdentifier: Identifier = {
    eat(Tokens.Underscore)
    val sym = parseSymbol

    val head = parseSExpr
    val indices = parseUntil(Tokens.CParen, eatEnd = false)(() => parseSExpr)

    Identifier(sym, head +: indices)
  }

  def parseAsIdentifier: QualifiedIdentifier = {
    eat(Tokens.As)
    val id = parseIdentifier
    val sort = parseSort
    QualifiedIdentifier(id, Some(sort))
  }

  def parseIdentifier: Identifier = {
    if(getPeekToken.kind == Tokens.OParen) {
      val pos = getPeekToken.getPos
      parseWithin(Tokens.OParen, Tokens.CParen)(() => parseUnderscoreIdentifier).setPos(pos)
    } else {
      val sym = parseSymbol
      Identifier(sym).setPos(sym)
    }
  }

  def parseSymbol: SSymbol = {
    nextToken() match {
      case t@Tokens.SymbolLit(s) => {
        val symbol = SSymbol(s)
        symbol.setPos(t)
      }
      case t => expected(t, Tokens.SymbolLitKind)
    }
  }
  
  /*
   * parse{String,Numeral,Decimal,Hexadecimal,Binary} are considered as 
   * terms in the trees, but technically they
   * can be used in many other situations (attribute values, command values)
   * so are rather part of Common parsers than just Term parsers.
   */

  def parseString: SString = {
    nextToken() match {
      case t@Tokens.StringLit(s) => {
        val str = SString(s)
        str.setPos(t)
      }
      case t => expected(t, Tokens.StringLitKind)
    }
  }

  def parseNumeral: SNumeral = {
    nextToken() match {
      case t@Tokens.NumeralLit(n) => {
        val num = SNumeral(n)
        num.setPos(t)
      }
      case token => expected(token, Tokens.NumeralLitKind)
    }
  }

  def parseDecimal: SDecimal = {
    nextToken() match {
      case t@Tokens.DecimalLit(n) => {
        val dec = SDecimal(n)
        dec.setPos(t)
      }
      case token => expected(token, Tokens.DecimalLitKind)
    }
  }

  def parseHexadecimal: SHexadecimal = {
    nextToken() match {
      case t@Tokens.HexadecimalLit(h) => {
        val hexa = SHexadecimal(h)
        hexa.setPos(t)
      }
      case token => expected(token, Tokens.HexadecimalLitKind)
    }
  }

  def parseBinary: SBinary = {
    nextToken() match {
      case t@Tokens.BinaryLit(b) => {
        val bin = SBinary(b.toList)
        bin.setPos(t)
      }
      case token => expected(token, Tokens.BinaryLitKind)
    }
  }

  def parseSList: SList = SList(parseMany(() => parseSExpr).toList)

  /**
    *
    * @note This is slighly inconsistent with the fact that Command and Term inherit
    *       from SExpr, in the sense that this will never return a Command or Term
    *       but rather returns the equivalent SList representation. So no
    *       {{{ SetLogic(QF_LIA) }}} but {{{ SList(SSymbol("set-logic"), SSymbol("QF_LIA")) }}}
    */
  def parseSExpr: SExpr = {
    getPeekToken.kind match {
      case Tokens.SymbolLitKind => parseSymbol
      case (word: Tokens.ReservedWord) => {
        nextToken()
        SSymbol(Tokens.reservedToSymbol(word))
      }
      case Tokens.NumeralLitKind => parseNumeral
      case Tokens.BinaryLitKind => parseBinary
      case Tokens.HexadecimalLitKind => parseHexadecimal
      case Tokens.DecimalLitKind => parseDecimal
      case Tokens.StringLitKind => parseString
      case Tokens.KeywordKind => parseKeyword
      case Tokens.OParen => parseSList
      case kind => 
        expected(peekToken, 
                 Tokens.SymbolLitKind, Tokens.NumeralLitKind, Tokens.BinaryLitKind,
                 Tokens.HexadecimalLitKind, Tokens.DecimalLitKind, Tokens.StringLitKind,
                 Tokens.KeywordKind, Tokens.OParen)
    }
  }


}
