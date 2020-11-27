package smtlib
package parser

import lexer.Tokens
import trees.Terms._
import trees.CommandsResponses._

import scala.collection.mutable.ListBuffer

trait ParserCommandsResponses { this: ParserCommon with ParserTerms with ParserCommands =>

  import Parser._

  /*
   * Parsing error response, assuming "(" has been parsed
   */
  private def parseErrorResponse: Error = {
    nextToken() match {
      case Tokens.SymbolLit("error") =>
        val msg = parseString.value
        eat(Tokens.CParen)
        Error(msg)
      case t => expected(t)
    }
  }

  def parseGenResponse: GenResponse = nextToken() match {
    case Tokens.SymbolLit("success") => Success
    case Tokens.SymbolLit("unsupported") => Unsupported
    case t =>
      check(t, Tokens.OParen)
      parseErrorResponse
  }

  def parseGetAssignmentResponse: GetAssignmentResponse = {
    def parsePair: (SSymbol, Boolean) = {
      eat(Tokens.OParen)
      val sym = parseSymbol
      val bool = parseBool
      eat(Tokens.CParen)
      (sym, bool)
    }

    nextToken() match {
      case Tokens.SymbolLit("unsupported") => Unsupported
      case t => {
        check(t, Tokens.OParen)
        peekToken match {
          case Tokens.SymbolLit("error") => parseErrorResponse
          case t => {
            val pairs = parseUntil(Tokens.CParen)(() => parsePair)
            GetAssignmentResponseSuccess(pairs)
          }
        }
      }
    }
  }

  def parseGetValueResponse: GetValueResponse = {
    def parsePair: (Term, Term) = {
      eat(Tokens.OParen)
      val t1 = parseTerm
      val t2 = parseTerm
      eat(Tokens.CParen)
      (t1, t2)
    }

    nextToken() match {
      case Tokens.SymbolLit("unsupported") => Unsupported
      case t => {
        check(t, Tokens.OParen)
        peekToken match {
          case Tokens.SymbolLit("error") => parseErrorResponse
          case t => {
            val pairs = parseUntil(Tokens.CParen)(() => parsePair)
            GetValueResponseSuccess(pairs)
          }
        }
      }
    }
  }

  def parseGetOptionResponse: GetOptionResponse = {
    tryParseConstant match {
      case Some(cst) => GetOptionResponseSuccess(cst)
      case None => {
        nextToken() match {
          case Tokens.SymbolLit("unsupported") => Unsupported
          case Tokens.SymbolLit(sym) => GetOptionResponseSuccess(SSymbol(sym))
          case t => {
            check(t, Tokens.OParen)
            peekToken match {
              case Tokens.SymbolLit("error") => parseErrorResponse
              case _ => GetOptionResponseSuccess(SList(parseUntil(Tokens.CParen)(() => parseSExpr).toList))
            }
          }
        }
      }
    }
  }

  def parseGetProofResponse: GetProofResponse = {
    tryParseConstant match {
      case Some(cst) => GetProofResponseSuccess(cst)
      case None => {
        nextToken() match {
          case Tokens.SymbolLit("unsupported") => Unsupported
          case Tokens.SymbolLit(sym) => GetProofResponseSuccess(SSymbol(sym))
          case Tokens.Keyword(key) => GetProofResponseSuccess(SKeyword(key))
          case t => {
            check(t, Tokens.OParen)
            peekToken match {
              case Tokens.SymbolLit("error") => parseErrorResponse
              case _ => GetProofResponseSuccess(SList(parseUntil(Tokens.CParen)(() => parseSExpr).toList))
            }
          }
        }
      }
    }
  }

  def parseGetModelResponse: GetModelResponse = {
    nextToken() match {
      case Tokens.SymbolLit("unsupported") => Unsupported
      case t => {
        check(t, Tokens.OParen)
        peekToken match {
          case Tokens.SymbolLit("error") => parseErrorResponse
          case t => {
            nextToken() match {
              case Tokens.SymbolLit("model") => ()
              case t => expected(t, Tokens.SymbolLitKind) //TODO: expected symbol of value "model"
            }
            val exprs: ListBuffer[SExpr] = new ListBuffer
            while(peekToken.kind != Tokens.CParen) {
              try {
                exprs.append(parseCommand)
              } catch {
                case ex: UnknownCommandException => {
                  ex.commandName match { //recover for exceptions case in get-model
                    case Tokens.Forall =>
                      val vars = parseMany(() => parseSortedVar)
                      val term = parseTerm
                      eat(Tokens.CParen)
                      exprs.append(Forall(vars.head, vars.tail, term))
                    case _ =>
                      throw ex
                  }
                }
              }
            }
            eat(Tokens.CParen)
            GetModelResponseSuccess(exprs.toList)
          }
        }
      }
    }
  }

  def parseInfoResponse: InfoResponse = {
    peekToken match {
      case Tokens.Keyword("assertion-stack-levels") =>
        nextToken()
        AssertionStackLevelsInfoResponse(parseNumeral.value.toInt)
      case Tokens.Keyword("authors") =>
        nextToken()
        AuthorsInfoResponse(parseString.value)
      case Tokens.Keyword("error-behavior") =>
        nextToken()
        val behaviour = nextToken() match {
          case Tokens.SymbolLit("immediate-exit") => ImmediateExitErrorBehavior
          case Tokens.SymbolLit("continued-execution") => ContinuedExecutionErrorBehavior
          case t => expected(t) //TODO: precise error
        }
        ErrorBehaviorInfoResponse(behaviour)
      case Tokens.Keyword("name") =>
        nextToken()
        NameInfoResponse(parseString.value)
      case Tokens.Keyword("reason-unknown") =>
        nextToken()
        val reason = nextToken() match {
          case Tokens.SymbolLit("timeout") => TimeoutReasonUnknown
          case Tokens.SymbolLit("memout") => MemoutReasonUnknown
          case Tokens.SymbolLit("incomplete") => IncompleteReasonUnknown
          case t => expected(t) //TODO: SMTLIB 2.5 allows arbitrary s-expr
        }
        ReasonUnknownInfoResponse(reason)
      case Tokens.Keyword("version") =>
        nextToken()
        VersionInfoResponse(parseString.value)
      case _ =>
        AttributeInfoResponse(parseAttribute)
    }
  }

  def parseGetInfoResponse: GetInfoResponse = {
    nextToken() match {
      case Tokens.SymbolLit("unsupported") => Unsupported
      case t => {
        check(t, Tokens.OParen)
        peekToken match {
          case Tokens.SymbolLit("error") => parseErrorResponse
          case t => {
            val responses = parseUntil(Tokens.CParen)(() => parseInfoResponse)
            GetInfoResponseSuccess(responses.head, responses.tail)
          }
        }
      }
    }
  }

  def parseCheckSatResponse: CheckSatResponse = {
    nextToken() match {
      case Tokens.SymbolLit("sat") => CheckSatStatus(SatStatus)
      case Tokens.SymbolLit("unsat") => CheckSatStatus(UnsatStatus)
      case Tokens.SymbolLit("unknown") => CheckSatStatus(UnknownStatus)
      case Tokens.SymbolLit("unsupported") => Unsupported
      case t => {
        check(t, Tokens.OParen)
        parseErrorResponse
      }
    }
  }

  def parseEchoResponse: EchoResponse = {
    nextToken() match {
      case Tokens.StringLit(value) => EchoResponseSuccess(value)
      case Tokens.SymbolLit("unsupported") => Unsupported
      case t => {
        check(t, Tokens.OParen)
        parseErrorResponse
      }
    }
  }

  def parseGetAssertionsResponse: GetAssertionsResponse = {
    nextToken() match {
      case Tokens.SymbolLit("unsupported") => Unsupported
      case t => {
        check(t, Tokens.OParen)
        peekToken match {
          case Tokens.SymbolLit("error") => parseErrorResponse
          case t => {
            val terms = parseUntil(Tokens.CParen)(() => parseTerm)
            GetAssertionsResponseSuccess(terms)
          }
        }
      }
    }
  }

  def parseGetUnsatAssumptionsResponse: GetUnsatAssumptionsResponse = {
    nextToken() match {
      case Tokens.SymbolLit("unsupported") => Unsupported
      case t => {
        check(t, Tokens.OParen)
        peekToken match {
          case Tokens.SymbolLit("error") => parseErrorResponse
          case t => {
            val syms = parseUntil(Tokens.CParen)(() => parseSymbol)
            GetUnsatAssumptionsResponseSuccess(syms)
          }
        }
      }
    }
  }

  def parseGetUnsatCoreResponse: GetUnsatCoreResponse = {
    nextToken() match {
      case Tokens.SymbolLit("unsupported") => Unsupported
      case t => {
        check(t, Tokens.OParen)
        peekToken match {
          case Tokens.SymbolLit("error") => parseErrorResponse
          case t => {
            val syms = parseUntil(Tokens.CParen)(() => parseSymbol)
            GetUnsatCoreResponseSuccess(syms)
          }
        }
      }
    }
  }
}
