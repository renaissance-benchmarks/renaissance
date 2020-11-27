package smtlib
package parser

import lexer.Tokens
import trees.Terms._
import trees.Commands._

import scala.collection.mutable.ListBuffer

trait ParserCommands { this: ParserCommon with ParserTerms =>

  import Parser._

  def parseScript: Script = {

    val cmds = new ListBuffer[Command]()
    var cmd = parseCommand
    while(cmd != null) {
      cmds.append(cmd)
      cmd = parseCommand
    }
    Script(cmds.toList)
  }

  protected def parseCommandWithoutParens: Command = nextToken().kind match {
    case Tokens.Assert => {
      Assert(parseTerm)
    }
    case Tokens.CheckSat => CheckSat()
    case Tokens.CheckSatAssuming => {
      val props = parseMany(() => parsePropLit)
      CheckSatAssuming(props)
    }

    case Tokens.DeclareConst => {
      val name = parseSymbol
      val sort = parseSort
      DeclareConst(name, sort)
    }
    case Tokens.DeclareFun => {
      val sym = parseSymbol

      val params = new ListBuffer[Sort]
      eat(Tokens.OParen)
      while(peekToken.kind != Tokens.CParen)
        params.append(parseSort)
      eat(Tokens.CParen)

      val sort = parseSort
      DeclareFun(sym, params.toList, sort)
    }
    case Tokens.DeclareSort => {
      val sym = parseSymbol
      val arity = parseNumeral
      DeclareSort(sym, arity.value.toInt)
    }

    case Tokens.DefineFun => {
      val funDef = parseFunDef
      DefineFun(funDef)
    }
    case Tokens.DefineFunRec => {
      val funDef = parseFunDef
      DefineFunRec(funDef)
    }
    case Tokens.DefineFunsRec => {
      val (funDef, funDefs) = parseOneOrMore(() => parseWithin(Tokens.OParen, Tokens.CParen)(() => parseFunDec))
      val (body, bodies) = parseOneOrMore(() => parseTerm)
      assert(funDefs.size == bodies.size)
      DefineFunsRec(funDef +: funDefs, body +: bodies)
    }
    case Tokens.DefineSort => {
      val sym = parseSymbol

      val vars = new ListBuffer[SSymbol]
      eat(Tokens.OParen)
      while(peekToken.kind != Tokens.CParen)
        vars.append(parseSymbol)
      eat(Tokens.CParen)

      val sort = parseSort
      DefineSort(sym, vars.toList, sort)
    }

    case Tokens.Echo => {
      val value = parseString
      Echo(value)
    }
    case Tokens.Exit => Exit()

    case Tokens.GetAssertions => GetAssertions()
    case Tokens.GetAssignment => GetAssignment()

    case Tokens.GetInfo => {
      val infoFlag = parseInfoFlag
      GetInfo(infoFlag)
    }

    case Tokens.GetModel => GetModel()

    case Tokens.GetOption => {
      val keyword = parseKeyword
      GetOption(keyword)
    }

    case Tokens.GetProof => GetProof()
    case Tokens.GetUnsatAssumptions => GetUnsatAssumptions()
    case Tokens.GetUnsatCore => GetUnsatCore()

    case Tokens.GetValue => {
      eat(Tokens.OParen)
      val ts = new ListBuffer[Term]
      while(peekToken.kind != Tokens.CParen)
        ts.append(parseTerm)
      eat(Tokens.CParen)
      GetValue(ts.head, ts.tail.toList)
    }

    case Tokens.Pop => {
      val n = parseNumeral
      Pop(n.value.toInt)
    }
    case Tokens.Push => {
      val n = parseNumeral
      Push(n.value.toInt)
    }

    case Tokens.Reset => Reset()
    case Tokens.ResetAssertions => ResetAssertions()

    case Tokens.SetInfo => {
      SetInfo(parseAttribute)
    }

    case Tokens.SetLogic => {
      val logicSymbol: SSymbol = parseSymbol
      val logic: Logic = 
        Logic.standardLogicFromString.lift(logicSymbol.name).getOrElse({
          logicSymbol match {
            case SSymbol("ALL") => ALL()
            case _ => NonStandardLogic(logicSymbol)
          }
        })
      SetLogic(logic.setPos(logicSymbol))
    }
    case Tokens.SetOption => {
      SetOption(parseOption)
    }

    case Tokens.DeclareDatatypes => {
      eat(Tokens.OParen)
      eat(Tokens.CParen)

      val datatypes = parseMany(() => parseDatatypes)

      DeclareDatatypes(datatypes)
    }

    case kind => {
      throw new UnknownCommandException(kind)
    }
  }

  def parseCommand: Command = if(peekToken == null) null else {
    val head = nextToken()
    check(head, Tokens.OParen)
    val cmd = parseCommandWithoutParens
    eat(Tokens.CParen)

    cmd.setPos(head)
  }

  def parsePropLit: PropLiteral = {
    peekToken.kind match {
      case Tokens.SymbolLitKind => {
        val sym = parseSymbol
        PropLiteral(sym, true).setPos(sym)
      }
      case Tokens.OParen => {
        val start = eat(Tokens.OParen)
        eat(Tokens.SymbolLit("not"))
        val sym = parseSymbol
        eat(Tokens.CParen)
        PropLiteral(sym, false).setPos(start)
      }
      case _ => {
        expected(peekToken, Tokens.SymbolLitKind, Tokens.OParen)
      }
    }
  }

  def parseFunDec: FunDec = {
    val name = parseSymbol

    val sortedVars = parseMany(() => parseSortedVar)

    val sort = parseSort

    FunDec(name, sortedVars, sort)
  }

  def parseFunDef: FunDef = {
    val name = parseSymbol

    val sortedVars = parseMany(() => parseSortedVar)

    val sort = parseSort

    val body = parseTerm

    FunDef(name, sortedVars, sort, body)
  }

  def parseDatatypes: (SSymbol, Seq[Constructor]) = {
    eat(Tokens.OParen)
    val name = parseSymbol
    val constructors = new ListBuffer[Constructor]
    while(peekToken.kind != Tokens.CParen) {
      constructors.append(parseConstructor)
    }
    eat(Tokens.CParen)
    (name, constructors.toSeq)
  }

  def parseConstructor: Constructor = {
    eat(Tokens.OParen)
    val name = parseSymbol

    val fields = new ListBuffer[(SSymbol, Sort)]
    while(peekToken.kind != Tokens.CParen) {
      eat(Tokens.OParen)
      val fieldName = parseSymbol
      val fieldSort = parseSort
      eat(Tokens.CParen)
      fields.append((fieldName, fieldSort))
    }
    eat(Tokens.CParen)

    Constructor(name, fields.toList)
  }


  def parseInfoFlag: InfoFlag = {
    val t = nextToken()
    val flag = t match {
      case Tokens.Keyword("all-statistics") => AllStatisticsInfoFlag()
      case Tokens.Keyword("assertion-stack-levels") => AssertionStackLevelsInfoFlag()
      case Tokens.Keyword("authors") => AuthorsInfoFlag()
      case Tokens.Keyword("error-behavior") => ErrorBehaviorInfoFlag()
      case Tokens.Keyword("name") => NameInfoFlag()
      case Tokens.Keyword("reason-unknown") => ReasonUnknownInfoFlag()
      case Tokens.Keyword("version") => VersionInfoFlag()
      case Tokens.Keyword(keyword) => KeywordInfoFlag(keyword)
      case t => expected(t, Tokens.KeywordKind)
    }
    flag.setPos(t)
  }


  def parseOption: SMTOption = {
    val peekPosition = peekToken.getPos
    val opt = peekToken match {
      case Tokens.Keyword("diagnostic-output-channel") => 
        nextToken()
        DiagnosticOutputChannel(parseString.value)

      case Tokens.Keyword("global-declarations") => 
        nextToken()
        GlobalDeclarations(parseBool)

      case Tokens.Keyword("interactive-mode") => 
        nextToken()
        InteractiveMode(parseBool)
      case Tokens.Keyword("print-success") =>
        nextToken()
        PrintSuccess(parseBool)

      case Tokens.Keyword("produce-assertions") => 
        nextToken()
        ProduceAssertions(parseBool)
      case Tokens.Keyword("produce-assignments") => 
        nextToken()
        ProduceAssignments(parseBool)
      case Tokens.Keyword("produce-models") => 
        nextToken()
        ProduceModels(parseBool)
      case Tokens.Keyword("produce-proofs") => 
        nextToken()
        ProduceProofs(parseBool)
      case Tokens.Keyword("produce-unsat-assumptions") => 
        nextToken()
        ProduceUnsatAssumptions(parseBool)
      case Tokens.Keyword("produce-unsat-cores") => 
        nextToken()
        ProduceUnsatCores(parseBool)

      case Tokens.Keyword("random-seed") => 
        nextToken()
        RandomSeed(parseNumeral.value.toInt)

      case Tokens.Keyword("regular-output-channel") => 
        nextToken()
        RegularOutputChannel(parseString.value)

      case Tokens.Keyword("reproducible-resource-limit") => 
        nextToken()
        ReproducibleResourceLimit(parseNumeral.value.toInt)
      case Tokens.Keyword("verbosity") => 
        nextToken()
        Verbosity(parseNumeral.value.toInt)

      case _ => 
        AttributeOption(parseAttribute)
    }
    opt.setPos(peekPosition)
  }

  def parseBool: Boolean = {
    nextToken() match {
      case Tokens.SymbolLit("true") => true
      case Tokens.SymbolLit("false") => false
      case t => expected(t) //TODO: not sure how to tell we were expecting one of two specific symbols
    }
  }


}
