package smtlib
package printer

import trees.Commands._
import trees.CommandsResponses._
import trees.Terms._
import trees.Tree

import java.io.Writer

class PrintingContext(writer: Writer) {

  final def output(tree: Tree): Unit = {
    start()
    print(tree)
    finish()
  }

  def print(tree: Tree): Unit = tree match {
    case term: Term => printTerm(term)
    case sort: Sort => printSort(sort)
    case cmd: Command => printCommand(cmd)
    case resp: CommandResponse => printCommandResponse(resp)
    case SList(es) => printNary(es, "(", " ", ")")
    case kw @ SKeyword(_) => printKeyword(kw)
    case s @ SSymbol(_) => printSymbol(s)
    case flag: InfoFlag => printInfoFlag(flag)
    case option: SMTOption => printOption(option)

    case attribute: Attribute =>
      printKeyword(attribute.keyword)
      attribute.value match {
        case Some(value) =>
          print(" ")
          print(value)
        case None => ()
      }

    case id: Identifier =>
      if (!id.isIndexed) {
        print(id.symbol)
      } else {
        print("(_ ")
        print(id.symbol)
        print(" ")
        print(id.indices.head)
        for (n <- id.indices.tail) {
          print(" ")
          print(n)
        }
        print(")")
      }

    case vb: VarBinding =>
      print("(")
      print(vb.name)
      print(" ")
      print(vb.term)
      print(")")

    case sv: SortedVar =>
      print("(")
      print(sv.name)
      print(" ")
      print(sv.sort)
      print(")")
  }

  def print(str: String): Unit = writer.write(str)

  protected def start(): Unit = ()
  protected def finish(): Unit = ()

  def printNary(trees: Seq[Tree], start: String, sep: String, end: String): Unit = {
    printNary(trees, print(_: Tree), start, sep, end)
  }

  def printNary[T](ts: Seq[T], p: T => Unit, start: String, sep: String, end: String): Unit = {
    print(start)

    var c = 0
    val sz = ts.size

    for (t <- ts) {
      p(t)
      c += 1
      if(c < sz) print(sep)
    }

    print(end)
  }

  private def printSymbol(sym: SSymbol): Unit = {
    val name = sym.name
    if (name.exists(c => !lexer.Lexer.isSymbolChar(c))) {
      print("|")
      print(name)
      print("|")
    } else {
      print(name)
    }
  }

  protected def printString(value: String): Unit = {
    print("\"")
    print(value.replaceAll("\"", "\"\""))
    print("\"")
  }

  private def printKeyword(keyword: SKeyword): Unit = {
    print(":")
    print(keyword.name)
  }

  private def printTerm(term: Term): Unit = term match {
    case Let(vb, vbs, t) =>
      print("(let (")
      print(vb)
      printNary(vbs, "", " ", ") ")
      print(t)
      print(")")

    case Forall(sortedVar, sortedVars, t) =>
      print("(forall (")
      print(sortedVar)
      printNary(sortedVars, "", " ", ") ")
      print(t)
      print(")")

    case Exists(sortedVar, sortedVars, t) =>
      print("(exists (")
      print(sortedVar)
      printNary(sortedVars, "", " ", ") ")
      print(t)
      print(")")

    case FunctionApplication(fun, ts) =>
      if (ts.nonEmpty) {
        print("(")
        print(fun)
        printNary(ts, " ", " ", ")")
      } else {
        print(fun)
      }

    case AnnotatedTerm(term, attr, attrs) =>
      print("(! ")
      print(term)
      printNary(attr +: attrs, " ", " ", ")")

    case QualifiedIdentifier(id, osort) => osort match {
      case Some(sort) =>
        print("(as ")
        print(id)
        print(" ")
        print(sort)
        print(")")

      case None =>
        print(id)
    }

    case SNumeral(value) => print(value.toString)
    case SHexadecimal(value) => print(value.toString)
    case SBinary(value) => print("#b" + value.map(if(_) "1" else "0").mkString)
    case SDecimal(value) => print(value.toString)
    case SString(value) => printString(value)

    case ext: TermExtension => ext.print(this)
  }

  private def printCommand(command: Command): Unit = command match {
    case Assert(term) =>
      print("(assert ")
      print(term)
      print(")\n")

    case CheckSat() =>
      print("(check-sat)\n")

    case CheckSatAssuming(props) =>
      print("(check-sat-assuming ")
      printNary(props, (prop: PropLiteral) => {
        if (prop.polarity) {
          print(prop.symbol)
        } else {
          print("(not ")
          print(prop.symbol)
          print(")")
        }
      }, "(", " ", ")")
      print(")\n")

    case DeclareConst(name, sort) =>
      print("(declare-const ")
      print(name)
      print(" ")
      print(sort)
      print(")\n")

    case DeclareFun(name, paramSorts, returnSort) =>
      print("(declare-fun ")
      print(name)
      printNary(paramSorts, " (", " ", ") ")
      print(returnSort)
      print(")\n")

    case DeclareSort(name, arity) =>
      print("(declare-sort ")
      print(name)
      print(" ")
      print(arity.toString)
      print(")\n")

    case DefineFun(FunDef(name, sortedVars, returnSort, body)) =>
      print("(define-fun ")
      print(name)
      printNary(sortedVars, " (", " ", ") ")
      print(returnSort)
      print(" ")
      print(body)
      print(")\n")

    case DefineFunRec(FunDef(name, sortedVars, returnSort, body)) =>
      print("(define-fun-rec ")
      print(name)
      printNary(sortedVars, " (", " ", ") ")
      print(returnSort)
      print(" ")
      print(body)
      print(")\n")

    case DefineFunsRec(funDecs, bodies) =>
      print("(define-funs-rec ")
      printNary(funDecs, (fd: FunDec) => {
        print("(")
        print(fd.name)
        printNary(fd.params, " (", " ", ") ")
        print(fd.returnSort)
        print(")")
      }, "(", " ", ")")
      printNary(bodies, " (", " ", ")")
      print(")\n")

    case DefineSort(name, params, sort) =>
      print("(define-sort ")
      print(name)
      printNary(params, " (", " ", ") ")
      print(sort)
      print(")\n")

    case Echo(value) =>
      print("(echo ")
      print(value)
      print(")\n")

    case Exit() =>
      print("(exit)\n")

    case GetAssertions() =>
      print("(get-assertions)\n")

    case GetAssignment() =>
      print("(get-assignment)\n")

    case GetInfo(flag) =>
      print("(get-info ")
      printInfoFlag(flag)
      print(")\n")

    case GetModel() =>
      print("(get-model)\n")

    case GetOption(SKeyword(key)) =>
      print("(get-option :")
      print(key)
      print(")\n")

    case GetProof() =>
      print("(get-proof)\n")

    case GetUnsatAssumptions() =>
      print("(get-unsat-assumptions)\n")

    case GetUnsatCore() =>
      print("(get-unsat-core)\n")

    case GetValue(t, ts) =>
      print("(get-value ")
      printNary(t +: ts, "(", " ", "))\n")

    case Pop(n) =>
      print("(pop ")
      print(n.toString)
      print(")\n")

    case Push(n) =>
      print("(push ")
      print(n.toString)
      print(")\n")

    case Reset() =>
      print("(reset)\n")

    case ResetAssertions() =>
      print("(reset-assertions)\n")

    case SetInfo(attribute) =>
      print("(set-info ")
      print(attribute)
      print(")\n")

    case SetOption(option) =>
      print("(set-option ")
      print(option)
      print(")\n")

    case SetLogic(logic) =>
      print("(set-logic ")
      logic match {
        case (std: StandardLogic) => print(Logic.asString(std))
        case NonStandardLogic(sym) => print(sym)
        case ALL() => print("ALL")
      }
      print(")\n")

    case ext: CommandExtension => ext.print(this)
  }

  private def printSort(sort: Sort): Unit = {
    val id = sort.id
    if(sort.subSorts.isEmpty)
      print(id)
    else {
      print("(")
      print(id)
      printNary(sort.subSorts, " ", " ", ")")
    }
  }

  protected def printCommandResponse(response: CommandResponse): Unit = response match {
    case Success => 
      print("success\n")

    case Unsupported =>
      print("unsupported\n")

    case Error(msg) =>
      print("(error ")
      print("\"")
      print(msg)
      print("\"")
      print(")\n")

    case CheckSatStatus(SatStatus) =>
      print("sat\n")

    case CheckSatStatus(UnsatStatus) =>
      print("unsat\n")

    case CheckSatStatus(UnknownStatus) =>
      print("unknown\n")

    case EchoResponseSuccess(value) =>
      printString(value)

    case GetAssertionsResponseSuccess(assertions) =>
      printNary(assertions, "(", " ", " )")

    case GetAssignmentResponseSuccess(valuationPairs) =>
      printNary(valuationPairs, (pair: (SSymbol, Boolean)) => {
        print("(")
        print(pair._1)
        print(" ")
        print(pair._2.toString)
        print(")")
      }, "(", " ", ")")

    case GetInfoResponseSuccess(response, responses) =>
      printNary(response +: responses, printInfoResponse, "(", " ", ")")

    case GetModelResponseSuccess(exprs) =>
      print("(model \n")
      printNary(exprs, "", "\n", "")
      print(")")

    case GetOptionResponseSuccess(av) =>
      print(av)

    case GetProofResponseSuccess(proof) =>
      print(proof)

    case GetUnsatAssumptionsResponseSuccess(symbols) =>
      printNary(symbols, "(", " ", ")")

    case GetUnsatCoreResponseSuccess(symbols) =>
      printNary(symbols, "(", " ", ")")

    case GetValueResponseSuccess(valuationPairs) =>
      printNary(valuationPairs, (pair: (Term, Term)) => {
        print("(")
        print(pair._1)
        print(" ")
        print(pair._2)
        print(")")
      }, "(", " ", ")")

    case ext: CommandResponseExtension => ext.print(this)
  }

  protected def printInfoFlag(flag: InfoFlag): Unit = flag match {
    case AllStatisticsInfoFlag() => print(":all-statistics")
    case AssertionStackLevelsInfoFlag() => print(":assertion-stack-level")
    case AuthorsInfoFlag() => print(":authors")
    case ErrorBehaviorInfoFlag() => print(":error-behavior")
    case NameInfoFlag() => print(":name")
    case ReasonUnknownInfoFlag() => print(":reason-unknown")
    case VersionInfoFlag() => print(":version")
    case KeywordInfoFlag(keyword) =>
      print(":")
      print(keyword)
  }

  protected def printOption(option: SMTOption): Unit = option match {
    case DiagnosticOutputChannel(value) =>
      print(":diagnostic-output-channel ")
      print("\"")
      print(value)
      print("\"")

    case GlobalDeclarations(value) =>
      print(":global-declarations ")
      print(value.toString)

    case InteractiveMode(value) =>
      print(":interactive-mode ")
      print(value.toString)

    case PrintSuccess(value) =>
      print(":print-success ")
      print(value.toString)

    case ProduceAssertions(value) =>
      print(":produce-assertions ")
      print(value.toString)

    case ProduceAssignments(value) =>
      print(":produce-assignments ")
      print(value.toString)

    case ProduceProofs(value) =>
      print(":produce-proofs ")
      print(value.toString)

    case ProduceModels(value) =>
      print(":produce-models ")
      print(value.toString)

    case ProduceUnsatAssumptions(value) =>
      print(":produce-unsat-assumptions ")
      print(value.toString)

    case ProduceUnsatCores(value) =>
      print(":produce-unsat-cores ")
      print(value.toString)

    case RegularOutputChannel(value) =>
      print(":regular-output-channel ")
      print("\"")
      print(value)
      print("\"")

    case RandomSeed(num) =>
      print(":random-seed ")
      print(num.toString)

    case ReproducibleResourceLimit(num) =>
      print(":reproducible-resource-limit ")
      print(num.toString)

    case Verbosity(num) =>
      print(":verbosity ")
      print(num.toString)

    case AttributeOption(attribute) =>
      print(attribute)

    case _ => ???
  }

  protected def printInfoResponse(infoResponse: InfoResponse): Unit = infoResponse match {
    case AssertionStackLevelsInfoResponse(level) =>
      print(":assertion-stack-levels ")
      print(level.toString)

    case AuthorsInfoResponse(authors) =>
      print(":authors ")
      printString(authors)

    case ErrorBehaviorInfoResponse(ImmediateExitErrorBehavior) =>
      print(":error-behavior immediate-exit")

    case ErrorBehaviorInfoResponse(ContinuedExecutionErrorBehavior) =>
      print(":error-behavior continued-execution")

    case NameInfoResponse(name) =>
      print(":name \"")
      print(name)
      print("\"")

    case ReasonUnknownInfoResponse(TimeoutReasonUnknown) =>
      print(":reason-unknown timeout")

    case ReasonUnknownInfoResponse(MemoutReasonUnknown) =>
      print(":reason-unknown memout")

    case ReasonUnknownInfoResponse(IncompleteReasonUnknown) =>
      print(":reason-unknown incomplete")

    case VersionInfoResponse(version) =>
      print(":version \"")
      print(version)
      print("\"")

    case AttributeInfoResponse(attribute) =>
      print(attribute)
  }
}
