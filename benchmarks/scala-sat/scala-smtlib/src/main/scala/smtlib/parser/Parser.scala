package smtlib
package parser

import lexer.Tokens
import Tokens.Token
import lexer.Lexer

import Terms._
import Commands._
import CommandsResponses._

import common._

import scala.collection.mutable.ListBuffer

class Parser(lexer: Lexer) {

  import Parser._

  private var _currentToken: Token = null
  /* lookAhead token is Some(null) if we reached eof */
  private var _lookAhead: Option[Token] = None

  //return a next token or null if EOF
  private def nextToken: Token = {
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
  private def peekToken: Token = {
    _lookAhead match {
      case Some(t) => t
      case None => {
        _lookAhead = Some(lexer.nextToken)
        _lookAhead.get
      }
    }
  }

  /*
   * Make sure the next token corresponds to t and read
   */
  private def eat(expected: Token): Unit = {
    val token = nextToken
    check(token, expected)
  }

  private def check(current: Token, exp: Token): Unit = {
    if(current != exp) {
      expected(exp, current)
    }
  }


  def parseCommand: Command = if(peekToken == null) null else {
    val head = nextToken
    check(head, Tokens.OParen())

    val cmd = nextToken match {
      case Tokens.SetLogic() => {
        val logicSymbol: SSymbol = parseSymbol
        val logic = Logic.fromString(logicSymbol.name)
        SetLogic(logic)
      }
      case Tokens.SetOption() => {
        SetOption(parseOption)
      }
      case Tokens.SetInfo() => {
        SetInfo(parseAttribute)
      }

      case Tokens.DeclareSort() => {
        val sym = parseSymbol
        val arity = parseNumeral
        DeclareSort(sym, arity.value.toInt)
      }
      case Tokens.DefineSort() => {
        val sym = parseSymbol

        val vars = new ListBuffer[SSymbol]
        eat(Tokens.OParen())
        while(peekToken != Tokens.CParen())
          vars.append(parseSymbol)
        eat(Tokens.CParen())

        val sort = parseSort
        DefineSort(sym, vars.toList, sort)
      }
      case Tokens.DeclareFun() => {
        val sym = parseSymbol

        val params = new ListBuffer[Sort]
        eat(Tokens.OParen())
        while(peekToken != Tokens.CParen())
          params.append(parseSort)
        eat(Tokens.CParen())

        val sort = parseSort
        DeclareFun(sym, params.toList, sort)
      }
      case Tokens.DefineFun() => {
        val name = parseSymbol

        val sortedVars = parseMany(parseSortedVar _)

        val sort = parseSort

        val body = parseTerm

        DefineFun(name, sortedVars, sort, body)
      }
      case Tokens.Push() => {
        val n = parseNumeral
        Push(n.value.toInt)
      }
      case Tokens.Pop() => {
        val n = parseNumeral
        Pop(n.value.toInt)
      }

      case Tokens.Assert() => {
        Assert(parseTerm)
      }

      case Tokens.CheckSat() => CheckSat()
      case Tokens.GetAssertions() => GetAssertions()
      case Tokens.GetProof() => GetProof()
      case Tokens.GetUnsatCore() => GetUnsatCore()
      case Tokens.GetValue() => {
        eat(Tokens.OParen())
        val ts = new ListBuffer[Term]
        while(peekToken != Tokens.CParen())
          ts.append(parseTerm)
        eat(Tokens.CParen())
        GetValue(ts.head, ts.tail.toList)
      }
      case Tokens.GetAssignment() => GetAssignment()

      case Tokens.GetOption() => {
        val keyword = parseKeyword
        GetOption(keyword)
      }
      case Tokens.GetInfo() => {
        val infoFlag = parseInfoFlag
        GetInfo(infoFlag)
      }

      case Tokens.Exit() => Exit()

      case Tokens.DeclareDatatypes() => {
        eat(Tokens.OParen())
        eat(Tokens.CParen())

        val datatypes = parseMany(parseDatatypes _)

        DeclareDatatypes(datatypes)
      }

      case t => {
        throw new UnknownCommandException(t)
      }
    }
    eat(Tokens.CParen())

    cmd.setPos(head)
  }

  def parseDatatypes: (SSymbol, Seq[Constructor]) = {
    eat(Tokens.OParen())
    val name = parseSymbol
    var constructors = new ListBuffer[Constructor]
    while(peekToken != Tokens.CParen()) {
      constructors.append(parseConstructor)
    }
    eat(Tokens.CParen())
    (name, constructors)
  }

  def parseConstructor: Constructor = {
    eat(Tokens.OParen())
    val name = parseSymbol

    var fields = new ListBuffer[(SSymbol, Sort)]
    while(peekToken != Tokens.CParen()) {
      eat(Tokens.OParen())
      val fieldName = parseSymbol
      val fieldSort = parseSort
      eat(Tokens.CParen())
      fields.append((fieldName, fieldSort))
    }
    eat(Tokens.CParen())

    Constructor(name, fields.toList)
  }

  def parseGenResponse: GenResponse = {
    nextToken match {
      case Tokens.SymbolLit("success") => Success
      case Tokens.SymbolLit("unsupported") => Unsupported
      case Tokens.OParen() => {
        nextToken match {
          case Tokens.SymbolLit("error") => {
            val msg = parseString.value
            eat(Tokens.CParen())
            Error(msg)
          }
          case _ => sys.error("TODO")
        }
      }
      case _ => sys.error("TODO")
    }
  }

  def parseGetAssignmentResponse: GetAssignmentResponse = {
    def parsePair: (SSymbol, Boolean) = {
      eat(Tokens.OParen())
      val sym = parseSymbol
      val bool = parseBool
      eat(Tokens.CParen())
      (sym, bool)
    }

    val pairs = parseMany(parsePair _)
    GetAssignmentResponse(pairs)
  }

  def parseGetValueResponse: GetValueResponse = {
    def parsePair: (Term, Term) = {
      eat(Tokens.OParen())
      val t1 = parseTerm
      val t2 = parseTerm
      eat(Tokens.CParen())
      (t1, t2)
    }

    val pairs = parseMany(parsePair _)
    GetValueResponse(pairs)
  }

  def parseGetOptionResponse: GetOptionResponse = {
    GetOptionResponse(parseSExpr)
  }

  def parseGetProofResponse: GetProofResponse = {
    GetProofResponse(parseSExpr)
  }

  def parseGetModelResponse: GetModelResponse = {
    eat(Tokens.OParen())
    eat(Tokens.SymbolLit("model"))
    var exprs: ListBuffer[SExpr] = new ListBuffer
    while(peekToken != Tokens.CParen()) {
      try {
        exprs.append(parseCommand)
      } catch {
        case ex: UnknownCommandException => {
          ex.commandName match { //recover for exceptions case in get-model
            case Tokens.ForAll() =>
              val vars = parseMany(parseSortedVar _)
              val term = parseTerm
              eat(Tokens.CParen())
              exprs.append(ForAll(vars.head, vars.tail, term))
            case _ =>
              throw ex
          }
        }
      }
    }
    eat(Tokens.CParen())
    GetModelResponse(exprs.toList)
  }

  def parseSExprResponse: SExprResponse = {
    eat(Tokens.OParen())
    var exprs = new ListBuffer[SExpr]
    while(peekToken != Tokens.CParen())
      exprs.append(parseSExpr)
    eat(Tokens.CParen())
    SExprResponse(SList(exprs.toList))
  }

  def parseInfoResponse: InfoResponse = {
    peekToken match {
      case Tokens.Keyword("error-behaviour") =>
        nextToken
        val behaviour = nextToken match {
          case Tokens.SymbolLit("immediate-exit") => ImmediateExitErrorBehaviour
          case Tokens.SymbolLit("continued-execution") => ContinueExecutionErrorBehaviour
          case _ => sys.error("TODO")
        }
        ErrorBehaviourInfoResponse(behaviour)
      case Tokens.Keyword("name") =>
        nextToken
        NameInfoResponse(parseString.value)
      case Tokens.Keyword("authors") =>
        nextToken
        AuthorsInfoResponse(parseString.value)
      case Tokens.Keyword("version") =>
        nextToken
        VersionInfoResponse(parseString.value)
      case Tokens.Keyword("reason-unknown") =>
        nextToken
        val reason = nextToken match {
          case Tokens.SymbolLit("timeout") => TimeoutReasonUnknown
          case Tokens.SymbolLit("memout") => MemoutReasonUnknown
          case Tokens.SymbolLit("incomplete") => IncompleteReasonUnknown
          case _ => sys.error("TODO")
        }
        ReasonUnkownionInfoResponse(reason)
      case _ =>
        AttributeInfoResponse(parseAttribute)
    }
  }

  def parseGetInfoResponse: GetInfoResponse = {
    val responses = parseMany(parseInfoResponse _)
    GetInfoResponse(responses.head, responses.tail)
  }

  def parseCheckSatResponse: CheckSatResponse = {
    nextToken match {
      case Tokens.SymbolLit("sat") => CheckSatResponse(SatStatus)
      case Tokens.SymbolLit("unsat") => CheckSatResponse(UnsatStatus)
      case Tokens.SymbolLit("unknown") => CheckSatResponse(UnknownStatus)
      case _ => sys.error("TODO")
    }
  }

  def parseGetAssertionsResponse: GetAssertionsResponse = {
    val terms = parseMany(parseTerm _)
    GetAssertionsResponse(terms)
  }

  def parseGetUnsatCoreResponse: GetUnsatCoreResponse = {
    val syms = parseMany(parseSymbol _)
    GetUnsatCoreResponse(syms)
  }

  def parseInfoFlag: InfoFlag = {
    nextToken match {
      case Tokens.Keyword("error-behaviour") => ErrorBehaviourInfoFlag
      case Tokens.Keyword("name") => NameInfoFlag
      case Tokens.Keyword("authors") => AuthorsInfoFlag
      case Tokens.Keyword("version") => VersionInfoFlag
      case Tokens.Keyword("status") => StatusInfoFlag
      case Tokens.Keyword("reason-unknown") => ReasonUnknownInfoFlag
      case Tokens.Keyword("all-statistics") => AllStatisticsInfoFlag
      case Tokens.Keyword(keyword) => KeywordInfoFlag(keyword)
      case _ => sys.error("TODO")
    }
  }

  def parseAttribute: Attribute = {
    val keyword = parseKeyword
    val attributeValue = tryParseAttributeValue
    Attribute(keyword, attributeValue)
  }

  def tryParseAttributeValue: Option[SExpr] = {
    peekToken match {
      case Tokens.NumeralLit(_) => Some(parseNumeral)
      case Tokens.BinaryLit(_) => Some(parseBinary)
      case Tokens.HexadecimalLit(_) => Some(parseHexadecimal)
      case Tokens.DecimalLit(_) => Some(parseDecimal)
      case Tokens.StringLit(_) => Some(parseString)
      case Tokens.SymbolLit(_) => Some(parseSymbol)
      case Tokens.OParen() => Some(parseSList)
      case _ => None
    }
  }

  def parseOption: SMTOption = {
    peekToken match {
      case Tokens.Keyword("print-success") =>
        nextToken
        PrintSuccess(parseBool)
      case Tokens.Keyword("expand-definitions") => 
        nextToken
        ExpandDefinitions(parseBool)
      case Tokens.Keyword("interactive-mode") => 
        nextToken
        InteractiveMode(parseBool)
      case Tokens.Keyword("produce-proofs") => 
        nextToken
        ProduceProofs(parseBool)
      case Tokens.Keyword("produce-unsat-cores") => 
        nextToken
        ProduceUnsatCores(parseBool)
      case Tokens.Keyword("produce-models") => 
        nextToken
        ProduceModels(parseBool)
      case Tokens.Keyword("produce-assignments") => 
        nextToken
        ProduceAssignments(parseBool)
      case Tokens.Keyword("regular-output-channel") => 
        nextToken
        RegularOutputChannel(parseString.value)
      case Tokens.Keyword("diagnostic-output-channel") => 
        nextToken
        DiagnosticOutputChannel(parseString.value)
      case Tokens.Keyword("random-seed") => 
        nextToken
        RandomSeed(parseNumeral.value.toInt)
      case Tokens.Keyword("verbosity") => 
        nextToken
        Verbosity(parseNumeral.value.toInt)
      case _ => 
        AttributeOption(parseAttribute)
    }
  }

  def parseBool: Boolean = {
    nextToken match {
      case Tokens.SymbolLit("true") => true
      case Tokens.SymbolLit("false") => false
      case _ => sys.error("TODO")
    }
  }

  def parseString: SString = {
    nextToken match {
      case t@Tokens.StringLit(s) => {
        val str = SString(s)
        str.setPos(t)
      }
      case _ => sys.error("TODO")
    }
  }
  def parseSymbol: SSymbol = {
    nextToken match {
      case t@Tokens.SymbolLit(s) => {
        val symbol = SSymbol(s)
        symbol.setPos(t)
      }
      case t => expected(Tokens.SymbolLit("x"), t) //TODO: expected should be of token class
    }
  }

  def parseNumeral: SNumeral = {
    nextToken match {
      case t@Tokens.NumeralLit(n) => {
        val num = SNumeral(n)
        num.setPos(t)
      }
      case _ => sys.error("TODO")
    }
  }

  def parseDecimal: SDecimal = {
    nextToken match {
      case t@Tokens.DecimalLit(n) => {
        val dec = SDecimal(n)
        dec.setPos(t)
      }
      case _ => sys.error("TODO")
    }
  }

  def parseKeyword: SKeyword = {
    nextToken match {
      case t@Tokens.Keyword(k) => {
        val keyword = SKeyword(k)
        keyword.setPos(t)
      }
      case _ => sys.error("TODO")
    }
  }

  def parseHexadecimal: SHexadecimal = {
    nextToken match {
      case t@Tokens.HexadecimalLit(h) => {
        val hexa = SHexadecimal(h)
        hexa.setPos(t)
      }
      case _ => sys.error("TODO")
    }
  }

  def parseBinary: SBinary = {
    nextToken match {
      case t@Tokens.BinaryLit(b) => {
        val bin = SBinary(b.toList)
        bin.setPos(t)
      }
      case _ => sys.error("TODO")
    }
  }

  def parseSort: Sort = {
    if(peekToken == Tokens.OParen()) {
      eat(Tokens.OParen())

      if(peekToken == Tokens.Underscore()) {
        val id = parseUnderscoreIdentifier
        Sort(id)
      } else {

        val name = parseIdentifier

        var subSorts = new ListBuffer[Sort]
        while(peekToken != Tokens.CParen())
          subSorts.append(parseSort)
        eat(Tokens.CParen())

        Sort(name, subSorts.toList)
      }
    } else {
      val id = parseIdentifier
      Sort(id)
    }
  }

  def parseUnderscoreIdentifier: Identifier = {
    eat(Tokens.Underscore())
    val sym = parseSymbol

    peekToken match {
      case Tokens.SymbolLit(_) => {
        val ext = parseSymbol
        eat(Tokens.CParen())
        ExtendedIdentifier(sym, ext)
      }
      case _ => {
        val firstIndex = parseNumeral.value.toInt
        var indices = new ListBuffer[Int]
        while(peekToken != Tokens.CParen())
          indices.append(parseNumeral.value.toInt)
        eat(Tokens.CParen())
        Identifier(sym, firstIndex :: indices.toList)
      }
    }
  }

  def parseQualifiedIdentifier: QualifiedIdentifier = {
    peekToken match {
      case Tokens.OParen() => {
        eat(Tokens.OParen())
        peekToken match {
          case Tokens.As() => {
            parseAsIdentifier
          }
          case Tokens.Underscore() => {
            QualifiedIdentifier(parseUnderscoreIdentifier)
          }
          case _ => sys.error("TODO")
        }
      }
      case _ => QualifiedIdentifier(parseIdentifier)
    }
  }

  def parseAsIdentifier: QualifiedIdentifier = {
    eat(Tokens.As())
    val id = parseIdentifier
    val sort = parseSort
    eat(Tokens.CParen())
    QualifiedIdentifier(id, Some(sort))
  }

  def parseIdentifier: Identifier = {
    if(peekToken == Tokens.OParen()) {
      eat(Tokens.OParen())
      parseUnderscoreIdentifier
    } else {
      val sym = parseSymbol
      Identifier(sym)
    }
  }

  def parseTerm: Term = { 
    if(peekToken == Tokens.OParen()) {
      eat(Tokens.OParen())

      peekToken match {
        case Tokens.Let() =>
          nextToken
          val bindings = parseMany(parseVarBinding _)
          val term = parseTerm
          eat(Tokens.CParen())
          Let(bindings.head, bindings.tail, term)
        case Tokens.ForAll() =>
          nextToken
          val vars = parseMany(parseSortedVar _)
          val term = parseTerm
          eat(Tokens.CParen())
          ForAll(vars.head, vars.tail, term)
        case Tokens.Exists() =>
          nextToken
          val vars = parseMany(parseSortedVar _)
          val term = parseTerm
          eat(Tokens.CParen())
          Exists(vars.head, vars.tail, term)

        case Tokens.ExclamationMark() =>
          nextToken
          val term = parseTerm
          val attrs = new ListBuffer[Attribute]
          while(peekToken != Tokens.CParen())
            attrs.append(parseAttribute)
          eat(Tokens.CParen())
          AnnotatedTerm(term, attrs.head, attrs.tail)

        case Tokens.As() =>
          parseAsIdentifier
        case Tokens.Underscore() =>
          QualifiedIdentifier(parseUnderscoreIdentifier)

        case _ => //should be function application
          val id = parseQualifiedIdentifier 

          val terms = new ListBuffer[Term]
          while(peekToken != Tokens.CParen())
            terms.append(parseTerm)
          eat(Tokens.CParen())
          FunctionApplication(id, terms.toList)
      }
    } else {
      val cst = tryParseConstant
      cst.getOrElse(QualifiedIdentifier(parseIdentifier))
    }
  }

  def parseVarBinding: VarBinding = {
    eat(Tokens.OParen())
    val sym = parseSymbol
    val term = parseTerm
    eat(Tokens.CParen())
    VarBinding(sym, term)
  }
  def parseSortedVar: SortedVar = {
    eat(Tokens.OParen())
    val sym = parseSymbol
    val sort = parseSort
    eat(Tokens.CParen())
    SortedVar(sym, sort)
  }

  /* Parse a sequence of A inside () */
  def parseMany[A](parseFun: () => A): Seq[A] = {
    val items = new ListBuffer[A]
    eat(Tokens.OParen())
    while(peekToken != Tokens.CParen())
      items.append(parseFun())
    eat(Tokens.CParen())
    items.toList
  }

  def tryParseConstant: Option[Constant] = {
    peekToken match {
      case Tokens.NumeralLit(_) => Some(parseNumeral)
      case Tokens.HexadecimalLit(_) => Some(parseHexadecimal)
      case Tokens.BinaryLit(_) => Some(parseBinary)
      case Tokens.DecimalLit(_) => Some(parseDecimal)
      case Tokens.StringLit(_) => Some(parseString)
      case _ => None
    }
  }

  def parseSList: SList = {
    eat(Tokens.OParen())
    var exprs = new ListBuffer[SExpr]
    while(peekToken != Tokens.CParen())
      exprs.append(parseSExpr)
    eat(Tokens.CParen())
    SList(exprs.toList)
  }


  def parseSExpr: SExpr = {
    peekToken match {
      case Tokens.SymbolLit(_) => parseSymbol
      case Tokens.NumeralLit(_) => parseNumeral
      case Tokens.BinaryLit(_) => parseBinary
      case Tokens.HexadecimalLit(_) => parseHexadecimal
      case Tokens.DecimalLit(_) => parseDecimal
      case Tokens.StringLit(_) => parseString
      case Tokens.Keyword(_) => parseKeyword
      case Tokens.OParen() => parseSList
      case _ => sys.error("TODO")
    }
  }

  //TODO: we need a token class/type, instead of precise token with content + position
  def expected(expected: Token, found: Token): Nothing = {
    throw new UnexpectedTokenException(expected, found)
  }

}

object Parser {

  class UnknownCommandException(val commandName: Token) extends Exception("Unknown command name token: " + commandName)
  class UnexpectedTokenException(expected: Token, found: Token) 
    extends Exception("Unexpected token at position: " + found.getPos + ". Expected: " + expected + ". Found: " + found)

  def fromString(str: String): Parser = {
    val lexer = new Lexer(new java.io.StringReader(str))
    new Parser(lexer)
  }

//  class EOFBeforeMatchingParenthesisException(startPos: Position) extends
//    Exception("Opened parenthesis at position: " + startPos + " has no matching closing parenthesis")
//  class UnexpectedTokenException(token: Token, pos: Position) extends
//    Exception("Unexpected token: " + token + " at position: " + pos)
//
//  def fromReader(reader: java.io.Reader): Parser = {
//    val lexer = new Lexer(reader)
//    new Parser(lexer)
//  }
//
//  /*
//   * Parse a string and return the next SExpr in the string, ignore the rest
//   */
//  def exprFromString(str: String): SExpr = {
//    val lexer = new Lexer(new java.io.StringReader(str))
//    val parser = new Parser(lexer)
//    parser.next
//  }
}
