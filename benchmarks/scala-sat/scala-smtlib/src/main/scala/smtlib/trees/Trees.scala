package smtlib
package trees

import common._
import printer._

sealed trait Tree extends Positioned

object Terms {

  /*
   * Many terms are case class X() with empty parameters list instead of being
   * the more usual case object X. The reason is that they eventually all inherit
   * from Positioned, which means they have a hidden Position attribute, and hence
   * we cannot share a unique global object for each syntax element.
   * Of course, I'm not happy with that solution, but I'm not sure what better
   * options we have.
   */

  /*
   * Identifier used to be indexed with Index type, that could be either SSymbol or SNumeral.
   * This is actually the current (2.5) SMT-LIB standard.
   * But in order to support some extensions in Z3, we use full SExpr as index.
   */
  sealed trait Index

  case class Identifier(symbol: SSymbol, indices: Seq[SExpr] = Seq()) extends Tree with Positioned {
    def isIndexed: Boolean = indices.nonEmpty
  }

  object SimpleIdentifier {
    def apply(symbol: SSymbol) = Identifier(symbol, Seq())
    def unapply(id: Identifier): Option[SSymbol] = id match {
      case Identifier(sym, Seq()) => Some(sym)
      case _ => None
    }
  }

  //(_ map or)
  object ExtendedIdentifier {
    
    def apply(symbol: SSymbol, extension: SSymbol) = Identifier(symbol, Seq(extension))
    
    def unapply(id: Identifier): Option[(SSymbol, SSymbol)] = id match {
      case Identifier(sym, Seq(ext@SSymbol(_))) => Some((sym, ext))
      case _ => None
    }
  }

  case class Sort(id: Identifier, subSorts: Seq[Sort]) extends Tree with Positioned {
    override def toString: String = printer.RecursivePrinter.toString(this)
  }

  object Sort {
    def apply(id: Identifier): Sort = Sort(id, Seq())
  }

  /* TODO
     Should we have an abstract class attribute and a bunch of predefined 
     attributes along with a default non-standard attribute? */
  case class Attribute(keyword: SKeyword, value: Option[AttributeValue]) extends Tree with Positioned
  object Attribute {
    def apply(key: SKeyword): Attribute = Attribute(key, None)
  }
  /*
   * An attribute value can either be
   *   - a list of SExpr
   *   - a SSymbol
   *   - a Constant
   * Note that if you want to create a Boolean (true/false) attribute value, you must
   * use SSymbol("true") or SSymbol("false"), due to the fact that boolean are not
   * considered syntactic constants in the SMT-LIB standard, but are represented by
   * symbols.
   */
  sealed trait AttributeValue extends SExpr

  case class SortedVar(name: SSymbol, sort: Sort) extends Tree with Positioned
  case class VarBinding(name: SSymbol, term: Term) extends Tree with Positioned

  sealed trait SExpr extends Tree with Positioned

  case class SList(sexprs: List[SExpr]) extends SExpr with AttributeValue
  object SList {
    def apply(sexprs: SExpr*): SList = SList(List(sexprs:_*))
  }
  case class SKeyword(name: String) extends SExpr
  case class SSymbol(name: String) extends SExpr with AttributeValue with Index

  /* SComment is never parsed, only used for pretty printing */
  // @nv XXX: this is actually never used...
  //case class SComment(s: String)

  sealed abstract class Term extends Positioned with SExpr {
    override def toString: String = printer.RecursivePrinter.toString(this)
  }

  case class Let(binding: VarBinding, bindings: Seq[VarBinding], term: Term) extends Term
  case class Forall(sortedVar: SortedVar, sortedVars: Seq[SortedVar], term: Term) extends Term
  case class Exists(sortedVar: SortedVar, sortedVars: Seq[SortedVar], term: Term) extends Term

  case class QualifiedIdentifier(id: Identifier, sort: Option[Sort]) extends Term
  object QualifiedIdentifier {
    def apply(id: Identifier): QualifiedIdentifier = QualifiedIdentifier(id, None)
  }

  case class AnnotatedTerm(term: Term, attribute: Attribute, attributes: Seq[Attribute]) extends Term
  case class FunctionApplication(fun: QualifiedIdentifier, terms: Seq[Term]) extends Term {
    //a function application with no argument is a qualified identifier
    require(terms.nonEmpty)
  }


  sealed trait Constant extends Term with AttributeValue

  /*
   * Literal do not necessarily have an associated expected meaning (SNumeral as an
   * integer or SBinary as a 2-complement integer). They are just syntactic units,
   * and each local theory gives them a semantics.
   *
   * For example, it means that
   * the decision that an SHexadecimal represents an bit-vector of 4*length(hexa) is
   * really up to the theory (in that case, the bit-vector theory), and each theory
   * could use hexadecimals as a different meaning.
   *
   * This is also why booleans are not considered literals. true/false are syntactically
   * simply symbols (SSymbol), and they don't need a particular syntax to represent them.
   */
  sealed trait Literal[T] extends Constant {
    val value: T
  }

  case class SNumeral(value: BigInt) extends Literal[BigInt] with Index
  case class SHexadecimal(value: Hexadecimal) extends Literal[Hexadecimal]
  case class SBinary(value: List[Boolean]) extends Literal[List[Boolean]]
  case class SDecimal(value: BigDecimal) extends Literal[BigDecimal]
  case class SString(value: String) extends Literal[String]

  /*
   * Special parent class for all non-standard terms.
   * See {{extensions/tip}} for an example.
   */
  abstract class TermExtension extends Term {
    def print(ctx: PrintingContext): Unit
  }
}

object Commands {
  import Terms._

  sealed abstract class Command extends Positioned with SExpr {
    override def toString: String = printer.RecursivePrinter.toString(this)
  }

  case class Script(commands: List[Command])

  case class Assert(term: Term) extends Command
  case class CheckSat() extends Command
  case class CheckSatAssuming(propLiterals: Seq[PropLiteral]) extends Command

  case class DeclareConst(name: SSymbol, sort: Sort) extends Command
  case class DeclareFun(name: SSymbol, paramSorts: Seq[Sort], returnSort: Sort) extends Command
  case class DeclareSort(name: SSymbol, arity: Int) extends Command
  case class DefineFun(funDef: FunDef) extends Command
  case class DefineFunRec(funDef: FunDef) extends Command
  case class DefineFunsRec(funDecls: Seq[FunDec], bodies: Seq[Term]) extends Command {
    require(funDecls.nonEmpty && funDecls.size == bodies.size)
  }
  case class DefineSort(name: SSymbol, params: Seq[SSymbol], sort: Sort) extends Command

  case class Echo(value: SString) extends Command

  case class Exit() extends Command

  case class GetAssertions() extends Command
  case class GetAssignment() extends Command
  case class GetInfo(flag: InfoFlag) extends Command
  case class GetModel() extends Command
  case class GetOption(key: SKeyword) extends Command
  case class GetProof() extends Command
  case class GetUnsatAssumptions() extends Command
  case class GetUnsatCore() extends Command
  case class GetValue(term: Term, terms: Seq[Term]) extends Command

  //TODO: should n be an SNumeral so that we can have a Position?
  case class Pop(n: Int) extends Command
  case class Push(n: Int) extends Command

  case class Reset() extends Command
  case class ResetAssertions() extends Command

  case class SetInfo(attribute: Attribute) extends Command
  case class SetLogic(logic: Logic) extends Command
  case class SetOption(option: SMTOption) extends Command

  /*
   * Special parent class for all non-standard commands.
   * See {{extensions/tip}} for an example.
   */
  abstract class CommandExtension extends Command {
    def print(ctx: PrintingContext): Unit

    def transform(tt: TreeTransformer)(context: tt.C): (Command, tt.R)
  }

  //non standard declare-datatypes (no support for parametric types)
  case class DeclareDatatypes(datatypes: Seq[(SSymbol, Seq[Constructor])]) extends CommandExtension {
    override def print(ctx: PrintingContext): Unit = {
      ctx.print("(declare-datatypes () ")
      ctx.printNary(datatypes, (datatype: (SSymbol, Seq[Constructor])) => {
        ctx.print("(")
        ctx.print(datatype._1.name)
        if (datatype._2.nonEmpty) ctx.printNary(datatype._2, (constructor: Constructor) => {
          ctx.print("(")
          ctx.print(constructor.sym.name)
          if (constructor.fields.nonEmpty) ctx.printNary(constructor.fields, (field: (SSymbol, Sort)) => {
            ctx.print("(")
            ctx.print(field._1.name)
            ctx.print(" ")
            ctx.print(field._2)
            ctx.print(")")
          }, " ", " ", "")
          ctx.print(")")
        }, " ", " ", "")
        ctx.print(")")
      }, "(", " ", "))\n")
    }

    override def transform(tt: TreeTransformer)(context: tt.C): (Command, tt.R) = {
      val (nds, rds) = datatypes.map(dt => transformDatatype(tt)(dt, context)).unzip
      (DeclareDatatypes(nds), tt.combine(this, context, rds.flatten))
    }

    private def transformDatatype(tt: TreeTransformer)
                  (datatype: (SSymbol, Seq[Constructor]), context: tt.C)
        : ((SSymbol, Seq[Constructor]), Seq[tt.R]) = {
      val (nameNew, nameRes) = tt.transformSymbol(datatype._1, context)
      val (constrsNew, constrsRes) = datatype._2.map(constr => {
        val (ns, rs) = tt.transformSymbol(constr.sym, context)
        val (nfs, rf) = constr.fields.map(field => {
          val (id, sort) = field
          val (nid, rid) = tt.transformSymbol(id, context)
          val (ns, rs) = tt.transform(sort, context)
          val newField = (nid, ns)
          (newField, Seq(rid, rs))
        }).unzip
        val newConstructor = Constructor(ns, nfs)
        (newConstructor, rs +: rf.flatten)
      }).unzip
      val newDatatype = (nameNew, constrsNew)
      (newDatatype, nameRes +: constrsRes.flatten)
    }
  }

  case class FunDec(name: SSymbol, params: Seq[SortedVar], returnSort: Sort)
  case class FunDef(name: SSymbol, params: Seq[SortedVar], returnSort: Sort, body: Term)
  //TODO: cannot get exact position of the polarity
  case class PropLiteral(symbol: SSymbol, polarity: Boolean) extends Positioned

  case class Constructor(sym: SSymbol, fields: Seq[(SSymbol, Sort)])

  /* 
   * Info flags can be queried with get-info command and
   * the SMT solver should support the following set of standard
   * flags. Additional solver-specific flags are supported via the general
   * KeywordInfoFlag
   */
  sealed abstract class InfoFlag extends Positioned
  case class AllStatisticsInfoFlag() extends InfoFlag
  case class AssertionStackLevelsInfoFlag() extends InfoFlag
  case class AuthorsInfoFlag() extends InfoFlag
  case class ErrorBehaviorInfoFlag() extends InfoFlag
  case class NameInfoFlag() extends InfoFlag
  case class ReasonUnknownInfoFlag() extends InfoFlag
  case class VersionInfoFlag() extends InfoFlag
  case class KeywordInfoFlag(keyword: String) extends InfoFlag

  /*
   * Options that can be passed to the underlying SMT solver.
   * A bunch of standard option (defined by the SMT-LIB standard) and
   * a generic syntax via attribute allows for solver-specific options
   */
  sealed abstract class SMTOption extends Tree with Positioned
  case class DiagnosticOutputChannel(value: String) extends SMTOption
  case class GlobalDeclarations(value: Boolean) extends SMTOption
  case class PrintSuccess(value: Boolean) extends SMTOption
  case class ProduceAssertions(value: Boolean) extends SMTOption
  case class ProduceAssignments(value: Boolean) extends SMTOption
  case class ProduceModels(value: Boolean) extends SMTOption
  case class ProduceProofs(value: Boolean) extends SMTOption
  case class ProduceUnsatAssumptions(value: Boolean) extends SMTOption
  case class ProduceUnsatCores(value: Boolean) extends SMTOption
  case class RandomSeed(value: Int) extends SMTOption
  case class RegularOutputChannel(value: String) extends SMTOption
  case class ReproducibleResourceLimit(value: Int) extends SMTOption
  case class Verbosity(value: Int) extends SMTOption
  case class AttributeOption(attribute: Attribute) extends SMTOption

  @deprecated("The solver option :interactive-mode has been renamed :produce-assertions. Use ProduceAssertions instead", "SMT-LIB 2.5")
  class InteractiveMode(val value: Boolean) extends SMTOption {

    override def equals(o: Any): Boolean = o != null && (o match {
      case (that: InteractiveMode) => this.value == that.value
      case _ => false
    })

    override def hashCode = value.hashCode
  }

  @deprecated("The solver option :interactive-mode has been renamed :produce-assertions. Use ProduceAssertions instead", "SMT-LIB 2.5")
  object InteractiveMode {
    def apply(value: Boolean) = new InteractiveMode(value)
    def unapply(opt: SMTOption): Option[Boolean] = opt match {
      case (im: InteractiveMode) => Some(im.value)
      case _ => None
    }
  }


  trait Logic extends Positioned

  /** A standard logic language */
  trait StandardLogic extends Logic

  case class AUFLIA() extends StandardLogic
  case class AUFLIRA() extends StandardLogic
  case class AUFNIRA() extends StandardLogic
  case class LRA() extends StandardLogic
  case class QF_ABV() extends StandardLogic
  case class QF_AUFBV() extends StandardLogic
  case class QF_AUFLIA() extends StandardLogic
  case class QF_AX() extends StandardLogic
  case class QF_BV() extends StandardLogic
  case class QF_IDL() extends StandardLogic
  case class QF_LIA() extends StandardLogic
  case class QF_LRA() extends StandardLogic
  case class QF_NIA() extends StandardLogic
  case class QF_NRA() extends StandardLogic
  case class QF_RDL() extends StandardLogic
  case class QF_UF() extends StandardLogic
  case class QF_UFBV() extends StandardLogic
  case class QF_UFIDL() extends StandardLogic
  case class QF_UFLIA() extends StandardLogic
  case class QF_UFLRA() extends StandardLogic
  case class QF_UFNRA() extends StandardLogic
  case class UFLRA() extends StandardLogic
  case class UFNIA() extends StandardLogic

  /** Most general logic supported by the solver */
  case class ALL() extends Logic

  /** A non-standard logic symbol supported by the solver */
  case class NonStandardLogic(sym: SSymbol) extends Logic

  object Logic {
    val standardLogicFromString: PartialFunction[String, StandardLogic] = {
      case "AUFLIA" => AUFLIA()
      case "AUFLIRA" => AUFLIRA()
      case "AUFNIRA" => AUFNIRA()
      case "LRA" => LRA()
      case "QF_ABV" => QF_ABV()
      case "QF_AUFBV" => QF_AUFBV()
      case "QF_AUFLIA" => QF_AUFLIA()
      case "QF_AX" => QF_AX()
      case "QF_BV" => QF_BV()
      case "QF_IDL" => QF_IDL()
      case "QF_LIA" => QF_LIA()
      case "QF_LRA" => QF_LRA()
      case "QF_NIA" => QF_NIA()
      case "QF_NRA" => QF_NRA()
      case "QF_RDL" => QF_RDL()
      case "QF_UF" => QF_UF()
      case "QF_UFBV" => QF_UFBV()
      case "QF_UFIDL" => QF_UFIDL()
      case "QF_UFLIA" => QF_UFLIA()
      case "QF_UFLRA" => QF_UFLRA()
      case "QF_UFNRA" => QF_UFNRA()
      case "UFLRA" => UFLRA()
      case "UFNIA" => UFNIA()
    }

    def asString(logic: Logic): String = logic match {
      case AUFLIA() => "AUFLIA"
      case AUFLIRA() => "AUFLIRA"
      case AUFNIRA() => "AUFNIRA"
      case LRA() => "LRA"
      case QF_ABV() => "QF_ABV"
      case QF_AUFBV() => "QF_AUFBV"
      case QF_AUFLIA() => "QF_AUFLIA"
      case QF_AX() => "QF_AX"
      case QF_BV() => "QF_BV"
      case QF_IDL() => "QF_IDL"
      case QF_LIA() => "QF_LIA"
      case QF_LRA() => "QF_LRA"
      case QF_NIA() => "QF_NIA"
      case QF_NRA() => "QF_NRA"
      case QF_RDL() => "QF_RDL"
      case QF_UF() => "QF_UF"
      case QF_UFBV() => "QF_UFBV"
      case QF_UFIDL() => "QF_UFIDL"
      case QF_UFLIA() => "QF_UFLIA"
      case QF_UFLRA() => "QF_UFLRA"
      case QF_UFNRA() => "QF_UFNRA"
      case UFLRA() => "UFLRA"
      case UFNIA() => "UFNIA"
      case ALL() => "ALL"
      case NonStandardLogic(sym) => sym.name
    }
  }

}


object CommandsResponses {
  import Terms._

  sealed abstract class CommandResponse extends Positioned with SExpr {
    override def toString: String = printer.RecursivePrinter.toString(this)
  }

  /*
   * A response can either be a successful response,
   * or one of Unsupported and Error.
   *
   * We define all the different possible responses categories as sealed trait
   * from which Unsupported and Error inherit. Additionnally each of the
   * trait have a concrete successful response that provide the response content.
   */

  /*
   * GenResponse is returned by some command, it's a basic Success object
   * for the successful kind, or Unsupported/Error
   */
  sealed trait GenResponse extends CommandResponse

  sealed trait CheckSatResponse extends CommandResponse
  sealed trait EchoResponse extends CommandResponse
  sealed trait GetAssertionsResponse extends CommandResponse
  sealed trait GetAssignmentResponse extends CommandResponse
  sealed trait GetInfoResponse extends CommandResponse
  sealed trait GetModelResponse extends CommandResponse
  sealed trait GetOptionResponse extends CommandResponse
  sealed trait GetProofResponse extends CommandResponse
  sealed trait GetUnsatAssumptionsResponse extends CommandResponse
  sealed trait GetUnsatCoreResponse extends CommandResponse
  sealed trait GetValueResponse extends CommandResponse


  sealed trait AllResponseKind extends GenResponse 
                               with CheckSatResponse with EchoResponse
                               with GetAssertionsResponse with GetAssignmentResponse 
                               with GetInfoResponse with GetModelResponse 
                               with GetOptionResponse with GetProofResponse
                               with GetUnsatAssumptionsResponse
                               with GetUnsatCoreResponse with GetValueResponse

  sealed trait SuccessfulResponse extends CommandResponse
  sealed trait FailureResponse extends CommandResponse with AllResponseKind

  case object Unsupported extends AllResponseKind with FailureResponse
  case class Error(msg: String) extends AllResponseKind with FailureResponse

  /*
   * All of the different successful response are of type SuccessfulResponse
   * As well as one of the response kind.
   */

  case object Success extends 
    GenResponse with SuccessfulResponse

  case class CheckSatStatus(status: Status) extends 
    CheckSatResponse with SuccessfulResponse

  case class EchoResponseSuccess(value: String) extends 
    EchoResponse with SuccessfulResponse

  case class GetAssertionsResponseSuccess(assertions: Seq[Term]) extends 
    GetAssertionsResponse with SuccessfulResponse

  case class GetAssignmentResponseSuccess(valuationPairs: Seq[(SSymbol, Boolean)]) extends
    GetAssignmentResponse with SuccessfulResponse

  case class GetInfoResponseSuccess(info: InfoResponse, infos: Seq[InfoResponse]) extends 
    GetInfoResponse with SuccessfulResponse

  /*
   * Z3 get-model. the model is a list of SExpr, but most S-Expr are actually well structured
   * like define-fun commands. We use SExpr as there are some Forall Term as well (which are
   * not the same type as Command)
   * TODO: SMTLIB 2.5 has a new standard for get-model
   */
  case class GetModelResponseSuccess(model: List[SExpr]) 
    extends GetModelResponse with SuccessfulResponse

  case class GetOptionResponseSuccess(attributeValue: AttributeValue) extends 
    GetOptionResponse with SuccessfulResponse

  case class GetProofResponseSuccess(proof: SExpr) extends 
    GetProofResponse with SuccessfulResponse

  case class GetUnsatAssumptionsResponseSuccess(symbols: Seq[SSymbol]) extends 
    GetUnsatAssumptionsResponse with SuccessfulResponse

  case class GetUnsatCoreResponseSuccess(symbols: Seq[SSymbol]) extends 
    GetUnsatCoreResponse with SuccessfulResponse

  case class GetValueResponseSuccess(valuationPairs: Seq[(Term, Term)]) extends 
    GetValueResponse with SuccessfulResponse

  abstract class CommandResponseExtension extends CommandResponse {
    def print(ctx: PrintingContext): Unit
  }


  /*
   * Helper types
   */
  sealed trait Status
  case object SatStatus extends Status
  case object UnsatStatus extends Status
  case object UnknownStatus extends Status

  sealed trait ErrorBehavior
  case object ImmediateExitErrorBehavior extends ErrorBehavior
  case object ContinuedExecutionErrorBehavior extends ErrorBehavior

  sealed trait ReasonUnknown
  case object TimeoutReasonUnknown extends ReasonUnknown
  case object MemoutReasonUnknown extends ReasonUnknown
  case object IncompleteReasonUnknown extends ReasonUnknown

  sealed trait InfoResponse
  case class AssertionStackLevelsInfoResponse(level: Int) extends InfoResponse
  case class AuthorsInfoResponse(authors: String) extends InfoResponse
  case class ErrorBehaviorInfoResponse(errorBehavior: ErrorBehavior) extends InfoResponse
  case class NameInfoResponse(name: String) extends InfoResponse
  case class ReasonUnknownInfoResponse(reason: ReasonUnknown) extends InfoResponse
  case class VersionInfoResponse(version: String) extends InfoResponse
  case class AttributeInfoResponse(attribute: Attribute) extends InfoResponse
}
