package smtlib
package lexer

import Tokens._
import common._

import scala.collection.mutable.ListBuffer

class Lexer(reader: java.io.Reader) {

  import Lexer._

  private def isNewLine(c: Char) = c == '\n' || c == '\r'
  private def isBlank(c: Char) = c == '\n' || c == '\r' || c == ' '
  private def isSeparator(c: Char) = isBlank(c) || c == ')' || c == '('

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
      case '(' => OParen()
      case ')' => CParen()
      case ':' => Keyword(readSymbol(nextChar))
      case '"' => {
        val buffer = new scala.collection.mutable.ArrayBuffer[Char]
        var c = nextChar
        while(c != '"') {
          if(c == '\\' && (peek == '"' || peek == '\\'))
            c = nextChar
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
          c = nextChar
        buffer.append(c)
        c = nextChar
      }
    } else {
      buffer.append(currentChar)
      while(isSymbolChar(peek.toChar) || peek == '\\') {
        if(peek == '\\') { //TODO: check what we should do here
          /*
	         * Escaped char was intended to be interpreted in its actual case.
	         * Probably not making a lot of sense in the SMT-LIB standard, but we
	         * are ignoring the backslash and recording the escaped char.
	         */
          nextChar
	      }
        buffer.append(nextChar)
      }
    }
    new String(buffer.toArray)
  }

  private def readInt(currentChar: Char, r: Int): BigInt = {
    require(r > 1 && r <= 36)
    var acc: BigInt = currentChar.asDigit //asDigit works for 'A', 'F', ...
    while(isDigit(peek.toChar, r)) {
      acc *= r
      acc += nextChar.asDigit
    }
    acc
  }

  private def readBinary(): Seq[Boolean] = {
    var res = new ListBuffer[Boolean]
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

  private var extraSymbolChars = Set('+', '-', '*', '/', '@', '$', '%', '^', '&', '_', 
                                     '!', '?', '[', ']', '{', '}', '=', '<', '>', '~', '.')
  private def isSymbolChar(c: Char): Boolean =
    c.isDigit || (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || extraSymbolChars.contains(c)

  private def isHexa(c: Char): Boolean =
    c.isDigit || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F')


  /* if c is digit in radix r (1 < r <= 36) */
  private def isDigit(c: Char, r: Int): Boolean = {
    require(r > 1 && r <= 36)
    val d = (c - '0').toInt
    if(d < 10 && d >= 0)
      d < r
    else {
      val ld = (c.toLower - 'a').toInt
      ld >= 0 && ld < r - 10
    }
  }

  private def toReserved(s: String): Option[Token] = s match {
    case "par" => Some(Par())
    case "NUMERAL" => Some(NUMERAL())
    case "DECIMAL" => Some(DECIMAL())
    case "STRING" => Some(STRING())
    case "_" => Some(Underscore())
    case "!" => Some(ExclamationMark())
    case "as" => Some(As())
    case "let" => Some(Let())
    case "forall" => Some(ForAll())
    case "exists" => Some(Exists())

    case "assert" => Some(Assert())
    case "check-sat" => Some(CheckSat())
    case "declare-sort" => Some(DeclareSort())
    case "declare-fun" => Some(DeclareFun())
    case "define-sort" => Some(DefineSort())
    case "define-fun" => Some(DefineFun())
    case "exit" => Some(Exit())
    case "get-assertions" => Some(GetAssertions())
    case "get-assignment" => Some(GetAssignment())
    case "get-info" => Some(GetInfo())
    case "get-option" => Some(GetOption())
    case "get-proof" => Some(GetProof())
    case "get-unsat-core" => Some(GetUnsatCore())
    case "get-value" => Some(GetValue())
    case "pop" => Some(Pop())
    case "push" => Some(Push())
    case "set-logic" => Some(SetLogic())
    case "set-info" => Some(SetInfo())
    case "set-option" => Some(SetOption())

    case "declare-datatypes" => Some(DeclareDatatypes())

    case _ => None
  }

}

object Lexer {

  class UnexpectedCharException(val char: Char, val position: Position, val msg: String) extends
    Exception("Encountered unexpected character: '" + char + "' at " + position + ": " + msg)

  class UnexpectedEOFException(val position: Position) extends Exception

}
