package smtlib
package parser

import parser.Terms._
import common._

object Commands {

  sealed abstract class Command extends Positioned with SExpr {
    override def toString: String = printer.PrettyPrinter.toString(this)
  }

  case class Script(commands: List[Command])

  case class SetLogic(logic: Logic) extends Command
  case class SetOption(option: SMTOption) extends Command
  case class SetInfo(attribute: Attribute) extends Command

  case class DeclareSort(name: SSymbol, arity: Int) extends Command
  case class DefineSort(name: SSymbol, params: Seq[SSymbol], sort: Sort) extends Command
  case class DeclareFun(name: SSymbol, paramSorts: Seq[Sort], returnSort: Sort) extends Command
  case class DefineFun(name: SSymbol, params: Seq[SortedVar], returnSort: Sort, body: Term) extends Command

  case class Push(n: Int) extends Command
  case class Pop(n: Int) extends Command
  case class Assert(term: Term) extends Command

  case class CheckSat() extends Command
  case class GetAssertions() extends Command
  case class GetProof() extends Command
  case class GetUnsatCore() extends Command
  case class GetValue(term: Term, terms: Seq[Term]) extends Command
  case class GetAssignment() extends Command

  case class GetOption(key: SKeyword) extends Command
  case class GetInfo(flag: InfoFlag) extends Command

  case class Exit() extends Command

  //this command can be used to create and print arbitrary commands using the s-expression
  //It can be used to send commands not supported in this library, such as non-standard commands like declare-datatypes
  case class NonStandardCommand(sexpr: SExpr) extends Command


  //z3 get-model
  case class GetModel() extends Command
  //non standard declare-datatypes (no support for parametric types)
  case class DeclareDatatypes(datatypes: Seq[(SSymbol, Seq[Constructor])]) extends Command

  case class Constructor(sym: SSymbol, fields: Seq[(SSymbol, Sort)])

  /* 
   * Info flags can be queried with get-info command and
   * the SMT solver should support the following set of standard
   * flags. Additional solver-specific flags are supported via the general
   * KeywordInfoFlag
   */
  sealed abstract class InfoFlag
  case object ErrorBehaviourInfoFlag extends InfoFlag
  case object NameInfoFlag extends InfoFlag
  case object AuthorsInfoFlag extends InfoFlag
  case object VersionInfoFlag extends InfoFlag
  case object StatusInfoFlag extends InfoFlag
  case object ReasonUnknownInfoFlag extends InfoFlag
  case object AllStatisticsInfoFlag extends InfoFlag
  case class KeywordInfoFlag(keyword: String) extends InfoFlag

  /*
   * Options that can be passed to the underlying SMT solver.
   * A bunch of standard option (defined by the SMT-LIB standard) and
   * a generic syntax via attribute allows for solver-specific options
   */
  sealed abstract class SMTOption
  case class PrintSuccess(value: Boolean) extends SMTOption
  case class ExpandDefinitions(value: Boolean) extends SMTOption
  case class InteractiveMode(value: Boolean) extends SMTOption
  case class ProduceProofs(value: Boolean) extends SMTOption
  case class ProduceUnsatCores(value: Boolean) extends SMTOption
  case class ProduceModels(value: Boolean) extends SMTOption
  case class ProduceAssignments(value: Boolean) extends SMTOption
  case class RegularOutputChannel(value: String) extends SMTOption
  case class DiagnosticOutputChannel(value: String) extends SMTOption
  case class RandomSeed(value: Int) extends SMTOption
  case class Verbosity(value: Int) extends SMTOption
  case class AttributeOption(attribute: Attribute) extends SMTOption


  sealed abstract class Logic
  case object QF_UF extends Logic
  case object QF_LRA extends Logic
  case object QF_AX extends Logic
  case object QF_A extends Logic
  case object Undef extends Logic

  object Logic {
    def fromString(logic: String): Logic = logic match {
      case "QF_UF"  => QF_UF
      case "QF_LRA" => QF_LRA
      case "QF_AX"  => QF_AX
      case "QF_A"   => QF_A
    }
  }

}
