package smtlib
package parser

import lexer._
import common._
import Commands._
import CommandsResponses._
import Terms._
import Parser._

import java.io.StringReader

import org.scalatest.FunSuite
import org.scalatest.concurrent.Timeouts
import org.scalatest.time.SpanSugar._

import scala.language.implicitConversions

class ParserTests extends FunSuite with Timeouts {

  override def suiteName = "SMT-LIB Parser suite"

  //parse the string for a single command and asserts no more commands
  private def parseUniqueCmd(str: String): Command = {
    val reader = new StringReader(str)
    val lexer = new Lexer(reader)
    val parser = new Parser(lexer)
    val cmd = parser.parseCommand
    assert(lexer.nextToken == null)
    cmd
  }


  def parseUniqueTerm(str: String): Term = {
    val reader = new StringReader(str)
    val lexer = new Lexer(reader)
    val parser = new Parser(lexer)
    val term = parser.parseTerm
    assert(lexer.nextToken == null)
    term
  }

  private implicit def strToSym(str: String): SSymbol = SSymbol(str)
  private implicit def strToId(str: String): Identifier = Identifier(SSymbol(str))
  private implicit def strToKeyword(str: String): SKeyword = SKeyword(str)
  private implicit def symToTerm(sym: SSymbol): QualifiedIdentifier = QualifiedIdentifier(sym.name)


  test("Parsing attributes") {
    def parseAttribute(str: String): Attribute = {
      val reader = new StringReader(str)
      val lexer = new Lexer(reader)
      val parser = new Parser(lexer)
      val attr = parser.parseAttribute
      attr
    }

    assert(parseAttribute(":test") === Attribute(SKeyword("test")))
    assert(parseAttribute(":key") === Attribute(SKeyword("key")))
    assert(parseAttribute(":abcd") === Attribute(SKeyword("abcd")))
    assert(parseAttribute(":test alpha") === Attribute(SKeyword("test"), Some(SSymbol("alpha"))))
    assert(parseAttribute(":test 42") === Attribute(SKeyword("test"), Some(SNumeral(42))))
    assert(parseAttribute(""":test "hello" """) === Attribute(SKeyword("test"), Some(SString("hello"))))
    assert(parseAttribute(""":test 23.12 """) === Attribute(SKeyword("test"), Some(SDecimal(23.12))))
    assert(parseAttribute(""":test (abc def) """) === 
                          Attribute(SKeyword("test"), 
                                    Some(SList(
                                          List(SSymbol("abc"), SSymbol("def"))))
                                   ))
    assert(parseAttribute(""":left-assoc""") === Attribute(SKeyword("left-assoc")))
    assert(parseAttribute(""":status unsat""") === Attribute(SKeyword("status"), Some(SSymbol("unsat"))))
    assert(parseAttribute(""":my_attribute (humpty dumpty)""") ===  
           Attribute(SKeyword("my_attribute"), Some(SList(List(SSymbol("humpty"), SSymbol("dumpty"))))))
    assert(parseAttribute(""":authors "Jack and Jill" """) === Attribute(SKeyword("authors"), Some(SString("Jack and Jill"))))
  }

  test("Parsing Sorts") {
    def parseSort(str: String): Sort = {
      val reader = new StringReader(str)
      val lexer = new Lexer(reader)
      val parser = new Parser(lexer)
      val sort = parser.parseSort
      sort
    }

    assert(parseSort("A") === Sort("A"))
    assert(parseSort("(A B)") === Sort("A", Seq(Sort("B"))))
    assert(parseSort("(Array From To)") === Sort("Array", Seq(Sort("From"), Sort("To"))))
    assert(parseSort("(_ A 42)") === Sort(Identifier("A", Seq(42))))
    assert(parseSort("(List (Array Int Real))") === 
                     Sort("List", Seq(
                                    Sort("Array", Seq(Sort("Int"), Sort("Real")))
                                  )
                         ))
    assert(parseSort("((_ FixedSizeList 4) Real)") === 
                     Sort(Identifier("FixedSizeList", Seq(4)), Seq(Sort("Real"))))
    assert(parseSort("(Set (_ Bitvec 3))") === Sort(Identifier("Set"), Seq(Sort(Identifier("Bitvec", Seq(3))))))



  }

  test("Parsing Identifiers") {
    def parseId(str: String): Identifier = {
      val reader = new StringReader(str)
      val lexer = new Lexer(reader)
      val parser = new Parser(lexer)
      val id = parser.parseIdentifier
      id
    }

    assert(parseId("abc") === Identifier("abc"))
    assert(parseId("test") === Identifier("test"))
    assert(parseId("(_ a 1)") === Identifier("a", Seq(1)))
    assert(parseId("(_ a 42 12)") === Identifier("a", Seq(42, 12)))

    //non standard syntax used by Z3 for extensions
    assert(parseId("(_ a sym)") === ExtendedIdentifier("a", SSymbol("sym")))
    assert(parseId("(_ map f)") === ExtendedIdentifier("map", SSymbol("f")))

  }

  test("Parsing simple Terms") {

    assert(parseUniqueTerm("42") === SNumeral(42))
    assert(parseUniqueTerm("42.12") === SDecimal(42.12))
    assert(parseUniqueTerm("#xF") === SHexadecimal(Hexadecimal.fromString("F").get))
    assert(parseUniqueTerm("#b1") === SBinary(List(true)))
    assert(parseUniqueTerm("abc") === QualifiedIdentifier("abc"))
    assert(parseUniqueTerm("(as abc A)") === QualifiedIdentifier("abc", Some(Sort("A"))))
    assert(parseUniqueTerm("(_ abc 42)") === QualifiedIdentifier(Identifier("abc", Seq(42))))
    assert(parseUniqueTerm("(as (_ abc 42) A)") === QualifiedIdentifier(Identifier("abc", Seq(42)), Some(Sort("A"))))
    assert(parseUniqueTerm("(f a b)") === 
           FunctionApplication(
            QualifiedIdentifier("f"), Seq(QualifiedIdentifier("a"), QualifiedIdentifier("b"))))
    assert(parseUniqueTerm("(let ((a x)) a)") ===
           Let(VarBinding("a", QualifiedIdentifier("x")), Seq(), QualifiedIdentifier("a")))

    assert(parseUniqueTerm("(forall ((a A)) a)") ===
           ForAll(SortedVar("a", Sort("A")), Seq(), QualifiedIdentifier("a"))
          )
    assert(parseUniqueTerm("(exists ((a A)) a)") ===
           Exists(SortedVar("a", Sort("A")), Seq(), QualifiedIdentifier("a"))
          )
    assert(parseUniqueTerm("(! a :note abcd)") ===
           AnnotatedTerm(QualifiedIdentifier("a"), Attribute(SKeyword("note"), Some(SSymbol("abcd"))), Seq())
          )

  }

  test("Parsing complicated terms") {
    assert(parseUniqueTerm("((_ f 1) a b)") === 
           FunctionApplication(
            QualifiedIdentifier(Identifier("f", Seq(1))),
            Seq(QualifiedIdentifier("a"), QualifiedIdentifier("b"))))

    assert(
      parseUniqueTerm("(let ((x 42)) (f x a))") ===
      Let(VarBinding("x", SNumeral(42)),
          Seq(),
          FunctionApplication(
            QualifiedIdentifier("f"), 
            Seq(QualifiedIdentifier("x"), QualifiedIdentifier("a")))))

    assert(
      parseUniqueTerm("(=> b (= e (as emptyset (Set Int))))") ===
      FunctionApplication(QualifiedIdentifier("=>"), Seq(
        QualifiedIdentifier("b"),
        FunctionApplication(QualifiedIdentifier("="), Seq(
          QualifiedIdentifier("e"),
          QualifiedIdentifier("emptyset", Some(Sort("Set", Seq(Sort("Int")))))
        ))
      ))
    )
  }

  test("Parsing single commands") {

    assert(parseUniqueCmd("(set-logic QF_UF)") === SetLogic(QF_UF))

    assert(parseUniqueCmd("(declare-sort A 0)") === DeclareSort("A", 0))
    assert(parseUniqueCmd("(define-sort A (B C) (Array B C))") ===
                          DefineSort("A", Seq("B", "C"), 
                                            Sort(Identifier("Array"), Seq(Sort("B"), Sort("C")))
                                    ))
    assert(parseUniqueCmd("(declare-fun xyz (A B) C)") ===
           DeclareFun("xyz", Seq(Sort("A"), Sort("B")), Sort("C")))
    assert(parseUniqueCmd("(define-fun f ((a A)) B a)") ===
           DefineFun("f", Seq(SortedVar("a", Sort("A"))), Sort("B"), QualifiedIdentifier("a")))

    assert(parseUniqueCmd("(push 1)") === Push(1))
    assert(parseUniqueCmd("(push 4)") === Push(4))
    assert(parseUniqueCmd("(pop 1)") === Pop(1))
    assert(parseUniqueCmd("(pop 2)") === Pop(2))
    assert(parseUniqueCmd("(assert true)") === Assert(QualifiedIdentifier("true")))
    assert(parseUniqueCmd("(check-sat)") === CheckSat())

    assert(parseUniqueCmd("(get-assertions)") === GetAssertions())
    assert(parseUniqueCmd("(get-proof)") === GetProof())
    assert(parseUniqueCmd("(get-unsat-core)") === GetUnsatCore())
    assert(parseUniqueCmd("(get-value (x y z))") === GetValue(SSymbol("x"), Seq(SSymbol("y"), SSymbol("z"))))
    assert(parseUniqueCmd("(get-assignment)") === GetAssignment())

    assert(parseUniqueCmd("(get-option :keyword)") === GetOption("keyword"))
    assert(parseUniqueCmd("(get-info :authors)") === GetInfo(AuthorsInfoFlag))

    assert(parseUniqueCmd("(exit)") === Exit())

    assert(parseUniqueCmd(
      "(declare-datatypes () ( (A (A1 (a1 Int) (a2 A)) (A2)) ))") ===
      DeclareDatatypes(Seq(
        (SSymbol("A"), Seq(Constructor("A1", 
                            Seq((SSymbol("a1"), Sort("Int")), (SSymbol("a2"), Sort("A")))),
                           Constructor("A2", Seq())
                          ))
      ))
    )
                        

  }

  test("Parsing set-option command") {
    assert(parseUniqueCmd("(set-option :print-success true)") === SetOption(PrintSuccess(true)))
    assert(parseUniqueCmd("(set-option :print-success false)") === SetOption(PrintSuccess(false)))
    assert(parseUniqueCmd("(set-option :expand-definitions true)") === SetOption(ExpandDefinitions(true)))
    assert(parseUniqueCmd("(set-option :expand-definitions false)") === SetOption(ExpandDefinitions(false)))
    assert(parseUniqueCmd("(set-option :interactive-mode true)") === SetOption(InteractiveMode(true)))
    assert(parseUniqueCmd("(set-option :interactive-mode false)") === SetOption(InteractiveMode(false)))
    assert(parseUniqueCmd("""(set-option :regular-output-channel "test")""") === 
                          SetOption(RegularOutputChannel("test")))
    assert(parseUniqueCmd("""(set-option :diagnostic-output-channel "toto")""") === 
                          SetOption(DiagnosticOutputChannel("toto")))
    assert(parseUniqueCmd("(set-option :random-seed 42)") === SetOption(RandomSeed(42)))
    assert(parseUniqueCmd("(set-option :verbosity 4)") === SetOption(Verbosity(4)))

  }

  test("Parsing set-info command") {
    assert(parseUniqueCmd("""(set-info :author "Reg")""") === SetInfo(Attribute(SKeyword("author"), Some(SString("Reg")))))
    assert(parseUniqueCmd("""(set-info :number 42)""") === SetInfo(Attribute(SKeyword("number"), Some(SNumeral(42)))))
    assert(parseUniqueCmd("""(set-info :test)""") === SetInfo(Attribute(SKeyword("test"), None)))
  }

  test("basic responses") {
    assert(Parser.fromString("success").parseGenResponse === Success)
    assert(Parser.fromString("unsupported").parseGenResponse === Unsupported)
    assert(Parser.fromString("(error \"this is an error\")").parseGenResponse === Error("this is an error"))

    assert(Parser.fromString("sat").parseCheckSatResponse === CheckSatResponse(SatStatus))
    assert(Parser.fromString("unsat").parseCheckSatResponse === CheckSatResponse(UnsatStatus))
    assert(Parser.fromString("unknown").parseCheckSatResponse === CheckSatResponse(UnknownStatus))

    assert(Parser.fromString("((a 1) (b 42))").parseGetValueResponse === GetValueResponse(Seq(
      (QualifiedIdentifier(Identifier("a")), SNumeral(1)), 
      (QualifiedIdentifier(Identifier("b")), SNumeral(42))
    )))

    assert(Parser.fromString("(model (define-fun z () Int 0))").parseGetModelResponse === 
      GetModelResponse(List(
        DefineFun("z", Seq(), Sort("Int"), SNumeral(0))))
    )

    assert(Parser.fromString(
"""(model 
  (define-fun z () Int 0)
  (declare-fun a () A)
  (forall ((x A)) x)
)""").parseGetModelResponse === 
      GetModelResponse(List(
        DefineFun("z", Seq(), Sort("Int"), SNumeral(0)),
        DeclareFun("a", Seq(), Sort("A")),
        ForAll(SortedVar("x", Sort("A")), Seq(), QualifiedIdentifier("x"))
      ))
    )
  }

  test("Unknown command") {
    val reader1 = new StringReader("(alpha beta)")
    val lexer1 = new Lexer(reader1)
    val parser1 = new Parser(lexer1)
    intercept[UnknownCommandException] {
      parser1.parseCommand
    }
  }

  test("simple benchmark") {
    val reader1 = new StringReader("""
      (set-logic QF_UF)
      (declare-fun f (Int) Int)
      (declare-fun a () Int)
      (assert (= (f a) a))
      (check-sat)
    """)
    val lexer1 = new Lexer(reader1)
    val parser1 = new Parser(lexer1)
    assert(parser1.parseCommand === SetLogic(QF_UF))
    assert(parser1.parseCommand === DeclareFun("f", Seq(Sort("Int")), Sort("Int")))
    assert(parser1.parseCommand === DeclareFun("a", Seq(), Sort("Int")))
    assert(parser1.parseCommand === 
           Assert(FunctionApplication(
                    QualifiedIdentifier("="),
                    Seq(
                      FunctionApplication(
                        QualifiedIdentifier("f"),
                        Seq(QualifiedIdentifier("a"))
                      ),
                      QualifiedIdentifier("a")
                    )
                  ))
           )
    assert(parser1.parseCommand === CheckSat())

  }

  test("interactive parser") {
    val pis = new SynchronousPipedReader
    val lexer = failAfter(3 seconds) { new Lexer(pis) }
    val parser = failAfter(3 seconds) { new Parser(lexer) }

    pis.write("(set-logic QF_LRA)")
    assert(parser.parseCommand === SetLogic(QF_LRA))

    pis.write("(assert (< 1 3))")
    assert(parser.parseCommand === 
           Assert(FunctionApplication(
             QualifiedIdentifier("<"),
             Seq(
               SNumeral(1), 
               SNumeral(3)
             )
           )))

  }

}
