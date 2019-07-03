package smtlib
package lexer

import common._


object Tokens {

  sealed abstract class Token extends Positioned

  /*
   * Need to be case class since each instance is different because of their positions
   * Alternatively, we could create a Token wrapper class that would be Positioned and
   * use the list of Tokens as a token information element.
   */
  case class OParen() extends Token /* ( */
  case class CParen() extends Token /* ) */

  case class StringLit(content: String) extends Token /* "hello" */

  case class SymbolLit(content: String) extends Token /* hello */
  case class Keyword(name: String) extends Token /* :bar */

  case class NumeralLit(n: BigInt) extends Token /* 42 */
  case class DecimalLit(d: Double) extends Token /* 42.24 */ //TODO: infinite precision ?
  case class BinaryLit(content: Seq[Boolean]) extends Token /* #b0101 */ 
  case class HexadecimalLit(content: Hexadecimal) extends Token /* #xFF1D */

  sealed trait ReservedWord extends Token
  case class Par() extends ReservedWord
  case class NUMERAL() extends ReservedWord
  case class DECIMAL() extends ReservedWord
  case class STRING() extends ReservedWord
  case class Underscore() extends ReservedWord /* _ */
  case class ExclamationMark() extends ReservedWord /* ! */
  case class As() extends ReservedWord /* as */
  case class Let() extends ReservedWord /* let */
  case class ForAll() extends ReservedWord /* forall */
  case class Exists() extends ReservedWord /* exists */

  case class Assert() extends ReservedWord
  case class CheckSat() extends ReservedWord
  case class DeclareSort() extends ReservedWord
  case class DeclareFun() extends ReservedWord
  case class DefineSort() extends ReservedWord
  case class DefineFun() extends ReservedWord
  case class Exit() extends ReservedWord
  case class GetAssertions() extends ReservedWord
  case class GetAssignment() extends ReservedWord
  case class GetInfo() extends ReservedWord
  case class GetOption() extends ReservedWord
  case class GetProof() extends ReservedWord
  case class GetUnsatCore() extends ReservedWord
  case class GetValue() extends ReservedWord
  case class Pop() extends ReservedWord
  case class Push() extends ReservedWord
  case class SetLogic() extends ReservedWord
  case class SetInfo() extends ReservedWord
  case class SetOption() extends ReservedWord

  case class DeclareDatatypes() extends ReservedWord

}
