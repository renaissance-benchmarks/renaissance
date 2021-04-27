package smtlib
package parser

import Parser._
import common._
import trees.Commands._
import trees.CommandsResponses._
import trees.Terms._

import org.scalatest.funsuite.AnyFunSuite

import scala.language.implicitConversions

class CommandsResponsesParserTests extends AnyFunSuite {

  private implicit def strToSym(str: String): SSymbol = SSymbol(str)
  private implicit def strToId(str: String): Identifier = Identifier(SSymbol(str))
  private implicit def strToKeyword(str: String): SKeyword = SKeyword(str)
  private implicit def symToTerm(sym: SSymbol): QualifiedIdentifier = QualifiedIdentifier(sym.name)


  override def suiteName = "SMT-LIB command response Parser suite"


  def checkFailureResponses(parse: (String) => CommandResponse): Unit = {
    assert(parse("unsupported") === Unsupported)
    assert(parse("(error \"msg\")") === Error("msg"))
    assert(parse("(error \"cool error\")") === Error("cool error"))
    assert(parse("(error \"this is an error\")") === Error("this is an error"))
    intercept[UnexpectedEOFException] {
      parse("(error \"cool error\"")
    }
  }


  test("Error response without a message should throw an unexpected token exception ") {
    intercept[UnexpectedTokenException] {
      Parser.fromString("(error)").parseGenResponse
    }
  }

  test("Error response without a closing paren should throw an unexpected eof exception ") {
    intercept[UnexpectedEOFException] {
      Parser.fromString("(error \"msg\"").parseGenResponse
    }
  }


  test("Parsing generic response") {
    checkFailureResponses(in => Parser.fromString(in).parseGenResponse)
    assert(Parser.fromString("success").parseGenResponse === Success)
  }


  /*
   * check-sat   
   */
  test("parsing check-sat response can be a failure response") {
    checkFailureResponses(in => Parser.fromString(in).parseCheckSatResponse)
  }

  test("Parsing check-sat response") {
    assert(Parser.fromString("sat").parseCheckSatResponse === CheckSatStatus(SatStatus))
    assert(Parser.fromString("unsat").parseCheckSatResponse === CheckSatStatus(UnsatStatus))
    assert(Parser.fromString("unknown").parseCheckSatResponse === CheckSatStatus(UnknownStatus))
  }

  /*
   * echo   
   */
  test("parsing echo response can be a failure response") {
    checkFailureResponses(in => Parser.fromString(in).parseEchoResponse)
  }
  test("Parsing echo response should not be symbol") {
    intercept[UnexpectedTokenException] {
      Parser.fromString(""" hey """).parseEchoResponse
    }
  }
  test("Parsing echo response") {
    assert(Parser.fromString(""" "Hello, World" """).parseEchoResponse === 
           EchoResponseSuccess("Hello, World"))
  }

  /*
   * get-assertions
   */
  test("Parsing get-assertions response can be a failure") {
    checkFailureResponses(in => Parser.fromString(in).parseGetAssertionsResponse)
  }

  test("Parsing get-assertions response") {
    assert(Parser.fromString("(42 a)").parseGetAssertionsResponse === 
      GetAssertionsResponseSuccess(Seq(SNumeral(42), QualifiedIdentifier("a"))))
    assert(Parser.fromString("(11.1 abcd \"alpha\")").parseGetAssertionsResponse === 
      GetAssertionsResponseSuccess(Seq(
        SDecimal(11.1), QualifiedIdentifier("abcd"), SString("alpha"))))
  }

  test("get-assertions can parse empty list of assertions") {
    assert(Parser.fromString("()").parseGetAssertionsResponse === 
      GetAssertionsResponseSuccess(Seq()))
  }

  /*
   * get-assignment
   */
  test("get-assignment response can be a failure") {
    checkFailureResponses(in => Parser.fromString(in).parseGetAssignmentResponse)
  }

  test("Parsing get-assignment response") {
    assert(Parser.fromString("((a true))").parseGetAssignmentResponse ===
      GetAssignmentResponseSuccess(Seq((SSymbol("a"), true))))
    assert(Parser.fromString("((b false))").parseGetAssignmentResponse ===
      GetAssignmentResponseSuccess(Seq((SSymbol("b"), false))))
    assert(Parser.fromString("((c true) (d false))").parseGetAssignmentResponse ===
      GetAssignmentResponseSuccess(Seq((SSymbol("c"), true), (SSymbol("d"), false))))
  }

  /*
   * get-info
   */
  test("Parsing get-info responses can be a failure response") {
    checkFailureResponses(in => Parser.fromString(in).parseGetInfoResponse)
  }

  test("Parsing get-info responses") {
    assert(
      Parser.fromString("""(:assertion-stack-levels 42)""").parseGetInfoResponse ===
      GetInfoResponseSuccess(AssertionStackLevelsInfoResponse(42), Seq())
    )
    assert(
      Parser.fromString("""(:authors "Regis Blanc")""").parseGetInfoResponse ===
      GetInfoResponseSuccess(AuthorsInfoResponse("Regis Blanc"), Seq())
    )
    assert(
      Parser.fromString("""(:error-behavior immediate-exit)""").parseGetInfoResponse ===
      GetInfoResponseSuccess(ErrorBehaviorInfoResponse(ImmediateExitErrorBehavior), Seq())
    )
    assert(
      Parser.fromString("""(:error-behavior continued-execution)""").parseGetInfoResponse ===
      GetInfoResponseSuccess(ErrorBehaviorInfoResponse(ContinuedExecutionErrorBehavior), Seq())
    )

    assert(
      Parser.fromString("""(:name "CafeSat")""").parseGetInfoResponse ===
      GetInfoResponseSuccess(NameInfoResponse("CafeSat"), Seq())
    )

    assert(
      Parser.fromString("""(:reason-unknown timeout)""").parseGetInfoResponse ===
      GetInfoResponseSuccess(ReasonUnknownInfoResponse(TimeoutReasonUnknown), Seq())
    )
    assert(
      Parser.fromString("""(:reason-unknown memout)""").parseGetInfoResponse ===
      GetInfoResponseSuccess(ReasonUnknownInfoResponse(MemoutReasonUnknown), Seq())
    )
    assert(
      Parser.fromString("""(:reason-unknown incomplete)""").parseGetInfoResponse ===
      GetInfoResponseSuccess(ReasonUnknownInfoResponse(IncompleteReasonUnknown), Seq())
    )

    assert(
      Parser.fromString("""(:version "2.0.1")""").parseGetInfoResponse ===
      GetInfoResponseSuccess(VersionInfoResponse("2.0.1"), Seq())
    )

    assert(
      Parser.fromString("""(:custom "abcd")""").parseGetInfoResponse ===
      GetInfoResponseSuccess(
        AttributeInfoResponse(
          Attribute(SKeyword("custom"), Some(SString("abcd")))),
        Seq())
    )
  }

  test("get-info response can be multiple info-response") {
    assert(
      Parser.fromString("""(:authors "Regis Blanc" :name "CafeSat")""").parseGetInfoResponse ===
      GetInfoResponseSuccess(AuthorsInfoResponse("Regis Blanc"), Seq(NameInfoResponse("CafeSat"))))
  }


  /*
   * get-model
   */
  test("Parsing get-model response can return failure responses") {
    checkFailureResponses(input => Parser.fromString(input).parseGetModelResponse)
  }

  test("Parsing get-model response") {
    assert(Parser.fromString("(model (define-fun z () Int 0))").parseGetModelResponse === 
      GetModelResponseSuccess(List(
        DefineFun(FunDef("z", Seq(), Sort("Int"), SNumeral(0)))))
    )

    assert(Parser.fromString(
"""(model 
      (define-fun x () Int 
          (- 1))
      )
""").parseGetModelResponse === 
      GetModelResponseSuccess(List(
        DefineFun(FunDef("x", Seq(), Sort("Int"), 
          FunctionApplication(QualifiedIdentifier("-"), Seq(SNumeral(1)))))))
    )

    assert(Parser.fromString(
"""(model 
  (define-fun z () Int 0)
  (declare-fun a () A)
  (forall ((x A)) x)
)""").parseGetModelResponse === 
      GetModelResponseSuccess(List(
        DefineFun(FunDef("z", Seq(), Sort("Int"), SNumeral(0))),
        DeclareFun("a", Seq(), Sort("A")),
        Forall(SortedVar("x", Sort("A")), Seq(), QualifiedIdentifier("x"))
      ))
    )
  }

  /*
   * get-option
   */
  test("Parsing get-option response can return failure responses") {
    checkFailureResponses(input => Parser.fromString(input).parseGetOptionResponse)
  }

  test("Parsing get-option constant responses") {
    assert(Parser.fromString("abcd").parseGetOptionResponse ===
      GetOptionResponseSuccess(SSymbol("abcd")))
    assert(Parser.fromString("42").parseGetOptionResponse ===
      GetOptionResponseSuccess(SNumeral(42)))
    assert(Parser.fromString("77.23").parseGetOptionResponse ===
      GetOptionResponseSuccess(SDecimal(77.23)))
    assert(Parser.fromString("#x1F").parseGetOptionResponse ===
      GetOptionResponseSuccess(SHexadecimal(Hexadecimal.fromString("1f").get)))
    assert(Parser.fromString("#b1011").parseGetOptionResponse ===
      GetOptionResponseSuccess(SBinary(List(true, false, true, true))))
    assert(Parser.fromString(""" "abcd" """).parseGetOptionResponse ===
      GetOptionResponseSuccess(SString("abcd")))
  }

  test("Parsing get-option response list expressions") {
    assert(Parser.fromString("(a 42)").parseGetOptionResponse ===
      GetOptionResponseSuccess(SList(SSymbol("a"), SNumeral(42))))
  }

  test("get-option response should not be a keyword") {
    intercept[UnexpectedTokenException] {
      Parser.fromString(":custom").parseGetOptionResponse
    }
  }


  /*
   * get-proof
   */
  test("get-proof response can be a failure") {
    checkFailureResponses(in => Parser.fromString(in).parseGetProofResponse)
  }

  test("get-proof response can be any s-expressions") {
    assert(Parser.fromString("42").parseGetProofResponse ===
      GetProofResponseSuccess(SNumeral(42)))
    assert(Parser.fromString("12.38").parseGetProofResponse ===
      GetProofResponseSuccess(SDecimal(12.38)))
    assert(Parser.fromString("#x1F").parseGetProofResponse ===
      GetProofResponseSuccess(SHexadecimal(Hexadecimal.fromString("1f").get)))
    assert(Parser.fromString("#b1011").parseGetProofResponse ===
      GetProofResponseSuccess(SBinary(List(true, false, true, true))))
    assert(Parser.fromString(":abcd").parseGetProofResponse ===
      GetProofResponseSuccess(SKeyword("abcd")))
    assert(Parser.fromString("(abc def 42)").parseGetProofResponse ===
      GetProofResponseSuccess(SList(SSymbol("abc"), SSymbol("def"), SNumeral(42))))
  }

  /*
   * get-unsat-assumptions
   */
  test("get-unsat-assumptions response can be a failure") {
    checkFailureResponses(in => Parser.fromString(in).parseGetUnsatAssumptionsResponse)
  }

  test("get-unsat-assumptions response can be an empty list of symbols") {
    assert(Parser.fromString("()").parseGetUnsatAssumptionsResponse === 
      GetUnsatAssumptionsResponseSuccess(Seq()))
  }

  test("get-unsat-assumptions response is a list of symbols") {
    assert(Parser.fromString("(x)").parseGetUnsatAssumptionsResponse === 
      GetUnsatAssumptionsResponseSuccess(Seq(SSymbol("x"))))
    assert(Parser.fromString("(a c)").parseGetUnsatAssumptionsResponse === 
      GetUnsatAssumptionsResponseSuccess(Seq(SSymbol("a"), SSymbol("c"))))
    assert(Parser.fromString("(a b c d)").parseGetUnsatAssumptionsResponse === 
      GetUnsatAssumptionsResponseSuccess(Seq(SSymbol("a"), SSymbol("b"), SSymbol("c"), SSymbol("d"))))
  }

  /*
   * get-unsat-core
   */
  test("get-unsat-core response can be a failure") {
    checkFailureResponses(in => Parser.fromString(in).parseGetUnsatCoreResponse)
  }

  test("get-unsat-core response can be an empty list of symbols") {
    assert(Parser.fromString("()").parseGetUnsatCoreResponse === 
      GetUnsatCoreResponseSuccess(Seq()))
  }

  test("get-unsat-core response is a list of symbols") {
    assert(Parser.fromString("(x)").parseGetUnsatCoreResponse === 
      GetUnsatCoreResponseSuccess(Seq(SSymbol("x"))))
    assert(Parser.fromString("(a c)").parseGetUnsatCoreResponse === 
      GetUnsatCoreResponseSuccess(Seq(SSymbol("a"), SSymbol("c"))))
    assert(Parser.fromString("(a b c d)").parseGetUnsatCoreResponse === 
      GetUnsatCoreResponseSuccess(Seq(SSymbol("a"), SSymbol("b"), SSymbol("c"), SSymbol("d"))))
  }

  /*
   * get-value
   */
  test("get-value response can be a failure") {
    checkFailureResponses(in => Parser.fromString(in).parseGetValueResponse)
  }

  test("Parsing get-value response") {
    assert(Parser.fromString("((x 13))").parseGetValueResponse ===
      GetValueResponseSuccess(Seq(
        (QualifiedIdentifier(Identifier("x")), SNumeral(13))
      ))
    ) 
    assert(Parser.fromString("((a 1) (b 42))").parseGetValueResponse ===
      GetValueResponseSuccess(Seq(
        (QualifiedIdentifier(Identifier("a")), SNumeral(1)), 
        (QualifiedIdentifier(Identifier("b")), SNumeral(42))
      ))
    )
  }

  /*
   * TODO: the standard requires at least one value, currently we return empty list
   */
  ignore("get-value response must contain at least one valuation pair") {
    intercept[UnexpectedTokenException] {
      Parser.fromString("()").parseGetValueResponse
    }
  }

}
