package smtlib
package lexer

import Tokens._
import common._

import scala.collection.mutable.ListBuffer

class Lexer(reader: java.io.Reader) {

  import Lexer._

  private def isNewLine(c: Char) = c == '\n' || c == '\r'
  private def isBlank(c: Char) = c == '\n' || c == '\r' || c == ' '

  /*
   * Note that we do not start reading the input until the next function is called.
   */
  private var _currentChar: Int = -1
  private var _futureChar: Option[Int] = None

  /*
   * Current line and column numbers of the current char value
   */
  private var _currentLine: Int = 1
  private var _currentCol: Int = 0

  /*
   * nextChar reads the next char in the reader and convert it into a char.
   * It raises an unexceptedEOFException if EOF is reached in the reader
   */
  private def nextChar: Char = {
    _futureChar match {
      case Some(i) => {
        if(i == -1)
          throw new UnexpectedEOFException(Position(_currentLine, _currentCol))
        _currentChar = i
        _futureChar = None
      }
      case None => {
        try {
          _currentChar = reader.read
        } catch {
          case e: java.io.EOFException => 
            throw new UnexpectedEOFException(Position(_currentLine, _currentCol))
        }
        if(_currentChar == -1)
          throw new UnexpectedEOFException(Position(_currentLine, _currentCol))
      }
    }

    val res = _currentChar.toChar
    if(isNewLine(res)) {
      _currentLine += 1
      _currentCol = 0
    } else {
      _currentCol += 1
    }
    res
  }

  //peek assumes that there should be something to read, encountering eof
  //should return -1, and the call should not be blocking
  private def peek: Int = _futureChar match {
    case Some(i) => i
    case None => {
      try {
        val tmp = reader.read
        _futureChar = Some(tmp)
        tmp
      } catch {
        case e: java.io.EOFException => -1
      }
    }
  }

  /* 
   * Return the next token if there is one, or null if EOF
   */
  def nextToken: Token = if(peek == -1) null else {

    var c: Char = nextChar

    while(isBlank(c) || c == ';') {

      if(c == ';') {
        while(!isNewLine(c)) {
          if(peek == -1)
            return null
          c = nextChar
        }
      }

      while(isBlank(c)) {
        if(peek == -1)
          return null
        c = nextChar
      }

    }

    val currentPosition = Position(_currentLine, _currentCol)

    val res: Token = c match {
      case '(' => Token(OParen)
      case ')' => Token(CParen)
      case ':' => Keyword(readSymbol(nextChar))
      case '"' => {
        val buffer = new scala.collection.mutable.ArrayBuffer[Char]
        var c = nextChar
        while(c != '"' || peek == '"') {
          if(c == '"') {
            assert(peek == '"')
            c = nextChar
          }
          buffer.append(c)
          c = nextChar
        }
        StringLit(new String(buffer.toArray))
      }
      case '#' => {
        nextChar match {
          case 'b' => BinaryLit(readBinary())
          case 'x' => HexadecimalLit(readHexadecimal())
          case c => {
            throw new UnexpectedCharException(c,
              Position(_currentLine, _currentCol), 
              "'#' should be followed by a radix 'b' or 'x'")
          }
        }
      }
      case d if d.isDigit => {
        val intPart = readInt(d, 10)
        if(peek != '.')
          NumeralLit(intPart)
        else {
          nextChar
          var fracPart: Double = 0
          var base = 10
          while(peek.toChar.isDigit) {
            fracPart += nextChar.asDigit
            fracPart *= 10
            base *= 10
          }
          DecimalLit(intPart.toDouble + fracPart/base)
        }
      }
      case s if isSymbolChar(s) || s == '|' => { //this case is after digits, since a symbol cannot start with a digit
        val sym = readSymbol(s)
        val res = toReserved(sym)
        res.getOrElse(SymbolLit(sym))
      }
      case c => {
        throw new UnexpectedCharException(c,
          Position(_currentLine, _currentCol), 
          "not a valid start for a token")
      }
    }

    res.setPos(currentPosition)
  }

  /*
   * Parse a symbol that can possibly starts with a digit.
   */
  //if this gets called for a full symbol, then we know that current char cannot be a
  //digit and hence we can ignore that case. If it gets called from keyword case, then
  //it might be a digit and this is fine according to the standard
  private def readSymbol(currentChar: Char): String = {
    val buffer = new scala.collection.mutable.ArrayBuffer[Char]
    if(currentChar == '|') { //a symbol can be within quotes: |symb|
      var c = nextChar
      while(c != '|') {
        if(c == '\\')
          throw new UnexpectedCharException(c, 
                                            Position(_currentLine, _currentCol),
                                            "Quoted symbols cannot contain backslashes")
        buffer.append(c)
        c = nextChar
      }
    } else {
      buffer.append(currentChar)
      while(isSymbolChar(peek.toChar)) {
        buffer.append(nextChar)
      }
    }
    new String(buffer.toArray)
  }

  private def readInt(currentChar: Char, r: Int): BigInt = {
    require(r > 1 && r <= 36)

    val pos = Position(_currentLine, _currentCol)

    var literal: String = currentChar.toString
    var acc: BigInt = currentChar.asDigit //asDigit works for 'A', 'F', ...
    while(isDigit(peek.toChar, r)) {
      acc *= r
      val c = nextChar
      acc += c.asDigit
      literal += c.toString
    }

    if(literal.head == '0' && literal.size > 1)
      throw new IllegalTokenException(literal, pos, "Numeral should not have leading 0")

    acc
  }

  private def readBinary(): Seq[Boolean] = {
    val res = new ListBuffer[Boolean]
    if(peek != '1' && peek != '0')
      throw new Exception
    while(peek == '1' || peek == '0') {
      res.append(if(peek == '1') true else false)
      nextChar
    }
    res.toList
  }

  private def readHexadecimal(): Hexadecimal = {
    var res = ""
    if(peek == -1 || !isHexa(peek.toChar))
      throw new Exception
    while(peek != -1 && isHexa(peek.toChar)) {
      res += nextChar.toUpper
    }
    Hexadecimal.fromString(res).get
  }


  protected def toReserved(s: String): Option[Token] = {
    val str2tok: PartialFunction[String, Token] = {
      case "BINARY" => Token(BINARY)
      case "DECIMAL" => Token(DECIMAL)
      case "HEXADECIMAL" => Token(HEXADECIMAL)
      case "NUMERAL" => Token(NUMERAL)
      case "STRING" => Token(STRING)
      case "_" => Token(Underscore)
      case "!" => Token(ExclamationMark)
      case "as" => Token(As)
      case "let" => Token(Let)
      case "forall" => Token(Forall)
      case "exists" => Token(Exists)
      case "par" => Token(Par)

      case "assert" => Token(Assert)
      case "check-sat" => Token(CheckSat)
      case "check-sat-assuming" => Token(CheckSatAssuming)
      case "declare-const" => Token(DeclareConst)
      case "declare-fun" => Token(DeclareFun)
      case "declare-sort" => Token(DeclareSort)
      case "define-fun" => Token(DefineFun)
      case "define-fun-rec" => Token(DefineFunRec)
      case "define-funs-rec" => Token(DefineFunsRec)
      case "define-sort" => Token(DefineSort)
      case "echo" => Token(Echo)
      case "exit" => Token(Exit)
      case "get-assertions" => Token(GetAssertions)
      case "get-assignment" => Token(GetAssignment)
      case "get-info" => Token(GetInfo)
      case "get-model" => Token(GetModel)
      case "get-option" => Token(GetOption)
      case "get-proof" => Token(GetProof)
      case "get-unsat-assumptions" => Token(GetUnsatAssumptions)
      case "get-unsat-core" => Token(GetUnsatCore)
      case "get-value" => Token(GetValue)
      case "pop" => Token(Pop)
      case "push" => Token(Push)
      case "reset" => Token(Reset)
      case "reset-assertions" => Token(ResetAssertions)
      case "set-info" => Token(SetInfo)
      case "set-logic" => Token(SetLogic)
      case "set-option" => Token(SetOption)

      case "declare-datatypes" => Token(DeclareDatatypes)
    }
    str2tok.lift(s)
  }

}

object Lexer {

  class UnexpectedCharException(val char: Char, val position: Position, val msg: String) extends
    Exception("Encountered unexpected character: '" + char + "' at " + position + ": " + msg)

  class UnexpectedEOFException(val position: Position) extends Exception

  class IllegalTokenException(val token: String, val position: Position, msg: String) extends Exception(s"Illegal token [$token] at $position: $msg")


  private val extraSymbolChars = Set('+', '-', '*', '/', '@', '$', '%', '^', '&',
                                     '_', '!', '?', '=', '<', '>', '~', '.')

  def isSymbolChar(c: Char): Boolean =
    c.isDigit || (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || extraSymbolChars.contains(c)

  def isHexa(c: Char): Boolean =
    c.isDigit || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F')


  /* if c is digit in radix r (1 < r <= 36) */
  def isDigit(c: Char, r: Int): Boolean = {
    require(r > 1 && r <= 36)
    val d = (c - '0')
    if(d < 10 && d >= 0)
      d < r
    else {
      val ld = (c.toLower - 'a')
      ld >= 0 && ld < r - 10
    }
  }
}
