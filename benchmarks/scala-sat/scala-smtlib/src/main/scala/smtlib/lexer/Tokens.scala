package smtlib
package lexer

import common._

object Tokens {

  sealed class Token(val kind: TokenKind) extends Positioned {
    override def toString = kind.toString
  }

  object Token {
    def apply(kind: TokenKind): Token = new Token(kind)
    def unapply(token: Token): Option[TokenKind] = Some(token.kind)
  }

  case class StringLit(content: String) extends Token(StringLitKind) {
    override def toString = "\"" + content + "\""
  }
  case class SymbolLit(content: String) extends Token(SymbolLitKind) {
    override def toString = s"$content"
  }
  case class Keyword(name: String) extends Token(KeywordKind) {
    override def toString = s":$name"
  }

  case class NumeralLit(n: BigInt) extends Token(NumeralLitKind) {
    override def toString = n.toString
  }
  case class DecimalLit(d: Double) extends Token(DecimalLitKind) {
    override def toString = d.toString
  }
  case class BinaryLit(content: Seq[Boolean]) extends Token(BinaryLitKind) {
    override def toString = content.map(d => if(d) "1" else "0").mkString
  }
  case class HexadecimalLit(content: Hexadecimal) extends Token(HexadecimalLitKind) {
    override def toString = content.toString
  }

  sealed trait TokenKind

  case object OParen extends TokenKind /* ( */
  case object CParen extends TokenKind /* ) */

  case object StringLitKind extends TokenKind /* "hello" */
  case object SymbolLitKind extends TokenKind /* hello */
  case object KeywordKind extends TokenKind /* :bar */
  case object NumeralLitKind extends TokenKind /* 42 */
  case object DecimalLitKind extends TokenKind /* 42.24 */
  case object BinaryLitKind extends TokenKind /* #b0101 */ 
  case object HexadecimalLitKind extends TokenKind /* #xFF1D */

  trait ReservedWord extends TokenKind
  case object BINARY extends ReservedWord
  case object DECIMAL extends ReservedWord
  case object HEXADECIMAL extends ReservedWord
  case object NUMERAL extends ReservedWord
  case object STRING extends ReservedWord
  case object Underscore extends ReservedWord /* _ */
  case object ExclamationMark extends ReservedWord /* ! */
  case object As extends ReservedWord /* as */
  case object Let extends ReservedWord /* let */
  case object Forall extends ReservedWord /* forall */
  case object Exists extends ReservedWord /* exists */
  case object Par extends ReservedWord

  case object Assert extends ReservedWord
  case object CheckSat extends ReservedWord
  case object CheckSatAssuming extends ReservedWord
  case object DeclareConst extends ReservedWord
  case object DeclareFun extends ReservedWord
  case object DeclareSort extends ReservedWord
  case object DefineFun extends ReservedWord
  case object DefineFunRec extends ReservedWord
  case object DefineFunsRec extends ReservedWord
  case object DefineSort extends ReservedWord
  case object Echo extends ReservedWord
  case object Exit extends ReservedWord
  case object GetAssertions extends ReservedWord
  case object GetAssignment extends ReservedWord
  case object GetInfo extends ReservedWord
  case object GetModel extends ReservedWord
  case object GetOption extends ReservedWord
  case object GetProof extends ReservedWord
  case object GetUnsatAssumptions extends ReservedWord
  case object GetUnsatCore extends ReservedWord
  case object GetValue extends ReservedWord
  case object Pop extends ReservedWord
  case object Push extends ReservedWord
  case object Reset extends ReservedWord
  case object ResetAssertions extends ReservedWord
  case object SetInfo extends ReservedWord
  case object SetLogic extends ReservedWord
  case object SetOption extends ReservedWord

  case object DeclareDatatypes extends ReservedWord

  def reservedToSymbol(word: ReservedWord): String = word match {
    case BINARY => "BINARY"
    case DECIMAL => "DECIMAL"
    case HEXADECIMAL => "HEXADECIMAl"
    case NUMERAL => "NUMERAL"
    case STRING => "STRING"
    case Underscore => "_"
    case ExclamationMark => "!"
    case As => "as"
    case Let => "let"
    case Forall => "forall"
    case Exists => "exists"
    case Par => "par"

    case Assert => "assert"
    case CheckSat => "check-sat"
    case CheckSatAssuming => "check-sat-assuming"
    case DeclareConst => "declare-const"
    case DeclareFun => "declare-fun"
    case DeclareSort => "ddeclare-sort"
    case DefineFun => "define-fun"
    case DefineFunRec => "define-fun-rec"
    case DefineFunsRec => "define-funs-rec"
    case DefineSort => "define-sort"
    case Echo => "echo"
    case Exit => "exit"
    case GetAssertions => "get-assertions"
    case GetAssignment => "get-assignment"
    case GetInfo => "get-info"
    case GetModel => "get-model"
    case GetOption => "get-option"
    case GetProof => "get-proof"
    case GetUnsatAssumptions => "get-unsat-assumptions"
    case GetUnsatCore => "get-unsat-core"
    case GetValue => "get-value"
    case Pop => "pop"
    case Push => "push"
    case Reset => "reset"
    case ResetAssertions => "reset-assetions"
    case SetInfo => "set-info"
    case SetLogic => "set-logic"
    case SetOption => "set-option"

    case DeclareDatatypes => "declare-datatypes"

  }
}
