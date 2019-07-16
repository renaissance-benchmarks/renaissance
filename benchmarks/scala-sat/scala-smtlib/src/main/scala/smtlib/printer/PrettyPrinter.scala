package smtlib
package printer

import parser.Commands._
import parser.CommandsResponses._
import parser.Terms._

import java.io.Writer
import java.io.StringWriter
import java.io.BufferedWriter

object PrettyPrinter {

  def toString(script: Script): String = {
    val output = new StringWriter
    val sWriter = new BufferedWriter(output)
    printScript(script, sWriter)
    sWriter.flush
    output.toString
  }

  def toString(command: Command): String = {
    val output = new StringWriter
    val sWriter = new BufferedWriter(output)
    printCommand(command, sWriter)
    sWriter.flush
    output.toString
  }

  def toString(term: Term): String = {
    val output = new StringWriter
    val sWriter = new BufferedWriter(output)
    printTerm(term, sWriter)
    sWriter.flush
    output.toString
  }

  def toString(sort: Sort): String = {
    val output = new StringWriter
    val sWriter = new BufferedWriter(output)
    printSort(sort, sWriter)
    sWriter.flush
    output.toString
  }

  def toString(response: CommandResponse): String = {
    val output = new StringWriter
    val sWriter = new BufferedWriter(output)
    printCommandResponse(response, sWriter)
    sWriter.flush
    output.toString
  }

  def printScript(script: Script, writer: Writer): Unit = ???

  def printCommand(command: Command, writer: Writer): Unit = command match {
    case SetLogic(logic) => {
      writer.write("(set-logic ")
      printLogic(logic, writer)
      writer.write(")\n")
    }
    case SetOption(option) => {
      writer.write("(set-option ")
      printOption(option, writer)
      writer.write(")\n")
    }
    case SetInfo(attribute) => {
      writer.write("(set-info ")
      printAttribute(attribute, writer)
      writer.write(")\n")
    }
    case DeclareSort(name, arity) => {
      writer.write("(declare-sort ")
      writer.write(name.name)
      writer.write(" ")
      writer.write(arity.toString)
      writer.write(")\n")
    }
    case DefineSort(name, params, sort) => {
      writer.write("(define-sort ")
      writer.write(name.name)
      writer.write(params.map(_.name).mkString(" (", " ", ") "))
      printSort(sort, writer)
      writer.write(")\n")
    }
    case DeclareFun(name, paramSorts, returnSort) => {
      writer.write("(declare-fun ")
      writer.write(name.name)
      printNary(writer, paramSorts, printSort _, " (", " ", ") ")
      printSort(returnSort, writer)
      writer.write(")\n")
    }
    case DefineFun(name, sortedVars, returnSort, body) => {
      writer.write("(define-fun ")
      writer.write(name.name)
      printNary(writer, sortedVars, printSortedVar _, " (", " ", ") ")
      printSort(returnSort, writer)
      writer.write(" ")
      printTerm(body, writer)
      writer.write(")\n")
    }
    case Push(n) => {
      writer.write("(push ")
      writer.write(n.toString)
      writer.write(")\n")
    }
    case Pop(n) => {
      writer.write("(pop ")
      writer.write(n.toString)
      writer.write(")\n")
    }
    case Assert(term) => {
      writer.write("(assert ")
      printTerm(term, writer)
      writer.write(")\n")
    }
    case CheckSat() => {
      writer.write("(check-sat)\n")
    }
    case GetAssertions() => {
      writer.write("(get-assertions)\n")
    }
    case GetProof() => {
     writer.write("(get-proof)\n")
    }
    case GetUnsatCore() => {
      writer.write("(get-unsat-core)\n")
    }
    case GetValue(t, ts) => {
      writer.write("(get-value ")
      printNary(writer, t +: ts, printTerm _, "(", " ", "))")
    }
    case GetAssignment() => {
      writer.write("(get-assignment)\n")
    }
    case GetOption(SKeyword(key)) => {
      writer.write("(get-option :")
      writer.write(key)
      writer.write(")\n")
    }
    case GetInfo(flag) => {
      writer.write("(get-info ")
      printInfoFlag(flag, writer)
      writer.write(")\n")
    }
    case Exit() => {
      writer.write("(exit)\n")
    }
    case NonStandardCommand(expr) => {
      printSExpr(expr, writer)
    }
    case GetModel() => {
      writer.write("(get-model)\n")
    }
    case DeclareDatatypes(datatypes) => {
      writer.write("(declare-datatypes () (")

      datatypes.foreach{ case (name, constructors) => {
        writer.write(" (")
        writer.write(name.name)
        constructors.foreach{ 
          case Constructor(sym, Seq()) => {
            writer.write(" (")
            writer.write(sym.name)
            writer.write(")")
          }
          case Constructor(sym, fields) => {
            writer.write(" (")
            writer.write(sym.name)
            fields.foreach{ case (field, sort) => {
              writer.write(" (")
              writer.write(field.name)
              writer.write(" ")
              printSort(sort, writer)
              writer.write(")")
            }}
            writer.write(")")
          }
        }
        writer.write(") ")
      }}

      writer.write("))\n")

    }
  }

  def printTerm(term: Term, writer: Writer): Unit = term match {
    case Let(vb, vbs, t) =>
      writer.write("(let (")
      printVarBinding(vb, writer)
      printNary(writer, vbs, printVarBinding _, "", " ", ") ")
      printTerm(t, writer)
      writer.write(")")
    case ForAll(sortedVar, sortedVars, t) =>
      writer.write("(forall (")
      printSortedVar(sortedVar, writer)
      printNary(writer, sortedVars, printSortedVar _, "", " ", ") ")
      printTerm(t, writer)
      writer.write(")")
    case Exists(sortedVar, sortedVars, t) =>
      writer.write("(exists (")
      printSortedVar(sortedVar, writer)
      printNary(writer, sortedVars, printSortedVar _, "", " ", ") ")
      printTerm(t, writer)
      writer.write(")")
    case FunctionApplication(fun, ts) =>
      writer.write("(")
      printQualifiedId(fun, writer)
      printNary(writer, ts, printTerm _, " ", " ", ")")
    case AnnotatedTerm(term, attr, attrs) => {
      writer.write("(! ")
      printTerm(term, writer)
      printNary(writer, attr +: attrs, printAttribute _, " ", " ", ")")
    }
    case id@QualifiedIdentifier(_, _) => 
      printQualifiedId(id, writer)

    case (c: Constant) => printConstant(c, writer)
  }

  def printConstant(c: Constant, writer: Writer): Unit = c match {
    case SNumeral(value) => writer.write(value.toString)
    case SHexadecimal(value) => writer.write(value.toString)
    case SBinary(value) => writer.write("#b" + value.map(if(_) "1" else "0").mkString)
    case SDecimal(value) => writer.write(value.toString)
    case SString(value) =>
      writer.write("\"")
      writer.write(value) //TODO: insert \"
      writer.write("\"")
  }

  def printQualifiedId(qi: QualifiedIdentifier, writer: Writer): Unit = qi.sort match {
    case None =>
      printId(qi.id, writer)
    case Some(sort) =>
      writer.write("(as ")
      printId(qi.id, writer)
      writer.write(" ")
      printSort(sort, writer)
      writer.write(")")
  }


  def printId(id: Identifier, writer: Writer): Unit = {
    if(id.indices.isEmpty)
      writer.write(id.symbol.name)
    else {
      writer.write("(_ ")
      writer.write(id.symbol.name)
      writer.write(' ')
      writer.write(id.indices.head.toString)
      id.indices.tail.foreach(n => writer.write(" " + n.toString))
      writer.write(")")
    }
  }

  def printVarBinding(vb: VarBinding, writer: Writer): Unit = {
    writer.write('(')
    writer.write(vb.name.name)
    writer.write(' ')
    printTerm(vb.term, writer)
    writer.write(')')
  }

  def printSortedVar(sv: SortedVar, writer: Writer): Unit = {
    writer.write('(')
    writer.write(sv.name.name)
    writer.write(' ')
    printSort(sv.sort, writer)
    writer.write(')')
  }

  private def printSort(sort: Sort, writer: Writer): Unit = {
    val id = sort.id
    if(sort.subSorts.isEmpty)
      printId(id, writer)
    else {
      writer.write("(")
      printId(id, writer)
      printNary(writer, sort.subSorts, printSort _, " ", " ", ")")
    }
  }

  private def printLogic(logic: Logic, writer: Writer): Unit = logic match {
    case QF_UF => 
      writer.write("QF_UF")
    case QF_LRA => 
      writer.write("QF_LRA")
    case QF_AX => 
      writer.write("QF_AX")
    case QF_A => 
      writer.write("QF_A")
    case Undef => ???
  }

  def printAttribute(attribute: Attribute, writer: Writer): Unit = {
    printKeyword(attribute.keyword, writer)
    attribute.v match {
      case Some(sexpr) => 
        writer.write(" ")
        printSExpr(sexpr, writer)
      case None => ()
    }
  }

  def printKeyword(keyword: SKeyword, writer: Writer): Unit = {
    writer.write(":")
    writer.write(keyword.name)
  }

  def printSExpr(sexpr: SExpr, writer: Writer): Unit = sexpr match {
    case SList(es) =>
      printNary(writer, es, printSExpr _, "(", " ", ")")
    case SKeyword(key) =>
      writer.write(":")
      writer.write(key)
    case SSymbol(sym) =>
      writer.write(sym)
    case _ => sys.error("TODO")
  }


  def printOption(option: SMTOption, writer: Writer): Unit = option match {
    case PrintSuccess(value) => 
      writer.write(":print-success ")
      writer.write(value.toString)
    case ExpandDefinitions(value) => 
      writer.write(":expand-definitions ")
      writer.write(value.toString)
    case InteractiveMode(value) => 
      writer.write(":interactive-mode ")
      writer.write(value.toString)
    case ProduceProofs(value) => 
      writer.write(":produce-proofs ")
      writer.write(value.toString)
    case ProduceUnsatCores(value) => 
      writer.write(":produce-unsat-cores ")
      writer.write(value.toString)
    case ProduceModels(value) => 
      writer.write(":produce-models ")
      writer.write(value.toString)
    case ProduceAssignments(value) => 
      writer.write(":produce-assignments ")
      writer.write(value.toString)
    case RegularOutputChannel(value) => 
      writer.write(":regular-output-channel ")
      writer.write('"')
      writer.write(value)
      writer.write('"')
    case DiagnosticOutputChannel(value) => 
      writer.write(":diagnostic-output-channel ")
      writer.write('"')
      writer.write(value)
      writer.write('"')
    case RandomSeed(num) => 
      writer.write(":random-seed ")
      writer.write(num.toString)
    case Verbosity(num) => 
      writer.write(":verbosity ")
      writer.write(num.toString)
    case AttributeOption(attribute) => 
      printAttribute(attribute, writer)
  }

  def printInfoFlag(flag: InfoFlag, writer: Writer): Unit = flag match {
    case ErrorBehaviourInfoFlag => 
      writer.write(":error-behaviour")
    case NameInfoFlag => 
      writer.write(":name")
    case AuthorsInfoFlag => 
      writer.write(":authors")
    case VersionInfoFlag => 
      writer.write(":version")
    case StatusInfoFlag => 
      writer.write(":status")
    case ReasonUnknownInfoFlag => 
      writer.write(":reason-unknonwn")
    case AllStatisticsInfoFlag => 
      writer.write(":all-statistics")
    case KeywordInfoFlag(keyword) =>
      writer.write(':')
      writer.write(keyword)
  }

  def printCommandResponse(response: CommandResponse, writer: Writer): Unit = response match {
    case Success => 
      writer.write("success\n")
    case Unsupported =>
      writer.write("unsupported\n")
    case Error(msg) =>
      writer.write("(error ")
      writer.write('"')
      writer.write(msg)
      writer.write('"')
      writer.write(")\n")
    case CheckSatResponse(SatStatus) =>
      writer.write("sat\n")
    case CheckSatResponse(UnsatStatus) =>
      writer.write("unsat\n")
    case CheckSatResponse(UnknownStatus) =>
      writer.write("unknown\n")

    case GetValueResponse(valuationPairs) =>
      def printValuationPair(pair: (Term, Term), writer: Writer): Unit = {
        writer.write('(')
        printTerm(pair._1, writer)
        writer.write(' ')
        printTerm(pair._2, writer)
        writer.write(')')
      }
      printNary(writer, valuationPairs, printValuationPair, "(", " ", ")")
    case _ => ???
  }

  private def printNary[A](
    writer: Writer, as: Seq[A], printer: (A, Writer) => Unit,
    pre: String, op: String, post: String): Unit = {

    writer.write(pre)

    var c = 0
    var sz = as.size

    as.foreach(a => {
      printer(a, writer)
      c += 1
      if(c < sz) writer.write(op)
    })
    writer.write(post)
  }

}
