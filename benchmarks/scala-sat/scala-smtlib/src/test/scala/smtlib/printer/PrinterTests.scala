package smtlib
package printer

import lexer.Lexer
import parser.Terms._
import parser.Commands._
import parser.CommandsResponses._
import parser.Parser

import common._

import java.io.StringReader

import org.scalatest.FunSuite

import scala.language.implicitConversions

class PrinterTests extends FunSuite {

  override def suiteName = "Printer suite"

  private implicit def strToSym(str: String): SSymbol = SSymbol(str)
  private implicit def strToId(str: String): Identifier = Identifier(SSymbol(str))
  private implicit def strToKeyword(str: String): SKeyword = SKeyword(str)
  private implicit def symToTerm(sym: SSymbol): QualifiedIdentifier = QualifiedIdentifier(sym.name)


  private def checkSort(sort: Sort): Unit = {

    val directPrint: String = PrettyPrinter.toString(sort)

    val parser = Parser.fromString(directPrint)
    val parsedAgain: Sort = parser.parseSort
    val printAgain: String = PrettyPrinter.toString(parsedAgain)

    assert(directPrint === printAgain)
    assert(sort === parsedAgain)
  }

  private def checkTerm(term: Term): Unit = {

    val directPrint: String = PrettyPrinter.toString(term)

    val parser = Parser.fromString(directPrint)
    val parsedAgain: Term = parser.parseTerm
    val printAgain: String = PrettyPrinter.toString(parsedAgain)

    assert(directPrint === printAgain)
    assert(term === parsedAgain)
  }

  private def checkCommand(cmd: Command): Unit = {

    val directPrint: String = PrettyPrinter.toString(cmd)

    val parser = Parser.fromString(directPrint)
    val parsedAgain: Command = parser.parseCommand
    val printAgain: String = PrettyPrinter.toString(parsedAgain)

    assert(directPrint === printAgain)
    assert(cmd === parsedAgain)
  }

  private def check[A](res: A, printer: (A) => String, parser: (String) => A): Unit = {

    val directPrint: String = printer(res)

    val parsedAgain: A = parser(directPrint)
    val printAgain: String = printer(parsedAgain)

    assert(directPrint === printAgain)
    assert(res === parsedAgain)
  }



  test("Printing simple Terms") {

    checkTerm(SNumeral(0))
    checkTerm(SNumeral(42))
    checkTerm(SHexadecimal(Hexadecimal.fromString("FF").get))
    checkTerm(SHexadecimal(Hexadecimal.fromString("123abcDeF").get))
    checkTerm(SBinary(List(true)))
    checkTerm(SBinary(List(true, false, true)))
    checkTerm(QualifiedIdentifier("abc"))
    checkTerm(FunctionApplication(
            QualifiedIdentifier("f"), Seq(QualifiedIdentifier("a"), QualifiedIdentifier("b"))))
    checkTerm(Let(VarBinding("a", QualifiedIdentifier("x")), Seq(), QualifiedIdentifier("a")))

    checkTerm(ForAll(SortedVar("a", Sort("A")), Seq(), QualifiedIdentifier("a")))
    checkTerm(Exists(SortedVar("a", Sort("A")), Seq(), QualifiedIdentifier("a")))
    checkTerm(AnnotatedTerm(QualifiedIdentifier("a"), Attribute(SKeyword("note"), Some(SSymbol("abcd"))), Seq()))

  }

  test("Printing composed Terms") {

  }

  test("Printing Sorts") {
    checkSort(Sort(Identifier(SSymbol("A"))))
    checkSort(Sort(Identifier(SSymbol("A"), Seq(42))))
    checkSort(Sort(Identifier(SSymbol("A"), Seq(42, 23))))
    checkSort(Sort(Identifier(SSymbol("A"), Seq(42, 23))))
    checkSort(Sort(Identifier(SSymbol("A")), Seq(Sort("B"), Sort("C"))))
  }

  test("Printing single commands") {

    checkCommand(SetLogic(QF_UF))

    checkCommand(DeclareSort("A", 0))
    checkCommand(DefineSort("A", Seq("B", "C"), 
                 Sort(Identifier("Array"), Seq(Sort("B"), Sort("C")))))
    checkCommand(DeclareFun("xyz", Seq(Sort("A"), Sort("B")), Sort("C")))
    checkCommand(DefineFun("f", Seq(SortedVar("a", Sort("A"))), Sort("B"), QualifiedIdentifier("a")))

    checkCommand(Push(1))
    checkCommand(Push(4))
    checkCommand(Pop(1))
    checkCommand(Pop(2))
    checkCommand(Assert(QualifiedIdentifier("true")))
    checkCommand(CheckSat())

    checkCommand(GetAssertions())
    checkCommand(GetProof())
    checkCommand(GetUnsatCore())
    checkCommand(GetValue(SSymbol("x"), Seq(SSymbol("y"), SSymbol("z"))))
    checkCommand(GetAssignment())

    checkCommand(GetOption("keyword"))
    checkCommand(GetInfo(AuthorsInfoFlag))

    checkCommand(Exit())
  }


  test("Printing Commands Reponses") {

    def printGenRes(res: GenResponse): String = PrettyPrinter.toString(res) 
    def parseGenRes(in: String): GenResponse = Parser.fromString(in).parseGenResponse
    check(Success, printGenRes, parseGenRes)
    check(Unsupported, printGenRes, parseGenRes)
    check(Error("symbol missing"), printGenRes, parseGenRes)

    def printGetAssignRes(res: GetAssignmentResponse): String = PrettyPrinter.toString(res)
    def parseGetAssignRes(in: String): GetAssignmentResponse = Parser.fromString(in).parseGetAssignmentResponse
    //TODO: some tests with get-assignment

    def printCheckSat(res: CheckSatResponse): String = PrettyPrinter.toString(res) 
    def parseCheckSat(in: String): CheckSatResponse = Parser.fromString(in).parseCheckSatResponse
    check(CheckSatResponse(SatStatus), printCheckSat, parseCheckSat)
    check(CheckSatResponse(UnsatStatus), printCheckSat, parseCheckSat)
    check(CheckSatResponse(UnknownStatus), printCheckSat, parseCheckSat)

    def printGetValue(res: GetValueResponse): String = PrettyPrinter.toString(res)
    def parseGetValue(in: String): GetValueResponse = Parser.fromString(in).parseGetValueResponse

    check(GetValueResponse(Seq( 
           (SSymbol("a"), SNumeral(42)) 
          )), printGetValue, parseGetValue)
    check(GetValueResponse(Seq( 
           (SSymbol("a"), SNumeral(42)), 
           (SSymbol("b"), SNumeral(12)) 
         )), printGetValue, parseGetValue)
  }


}
