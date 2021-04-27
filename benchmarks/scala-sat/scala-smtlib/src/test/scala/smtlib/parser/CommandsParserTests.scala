package smtlib
package parser

import lexer._
import Parser._
import common._
import trees.Tree
import trees.Commands._
import trees.Terms._
import trees.TreesOps

import java.io.StringReader

import org.scalatest.concurrent.TimeLimits
import org.scalatest.funsuite.AnyFunSuite

import scala.language.implicitConversions

class CommandsParserTests extends AnyFunSuite with TimeLimits {

  override def suiteName = "SMT-LIB commands Parser suite"


  //parse the string for a single command and asserts no more commands
  private def parseUniqueCmd(str: String): Command = {
    val reader = new StringReader(str)
    val lexer = new Lexer(reader)
    val parser = new Parser(lexer)
    val cmd = parser.parseCommand
    assert(lexer.nextToken == null)
    assertEachNodeHasPos(cmd)
    cmd
  }

  private implicit def strToSym(str: String): SSymbol = SSymbol(str)
  private implicit def strToId(str: String): Identifier = Identifier(SSymbol(str))
  private implicit def strToKeyword(str: String): SKeyword = SKeyword(str)
  private implicit def symToTerm(sym: SSymbol): QualifiedIdentifier = QualifiedIdentifier(sym.name)
  private implicit def intToNum(n: Int): SNumeral = SNumeral(n)
  private implicit def IntSeqToIndices(ns: Seq[Int]): Seq[Index] = ns.map(n => SNumeral(n))



  test("Parsing assert commands") {
    assert(parseUniqueCmd("(assert true)") === 
           Assert(QualifiedIdentifier("true")))
    assert(parseUniqueCmd("(assert (p 42))") === 
           Assert(FunctionApplication(QualifiedIdentifier("p"), 
                  Seq(SNumeral(42)))))
  }

  test("Parsing assert without term throws UnexpectedTokenException") {
    intercept[UnexpectedTokenException] {
      parseUniqueCmd("(assert)")
    }
  }

  test("Parsing check-sat command") {
    assert(parseUniqueCmd("(check-sat)") === CheckSat())
  }

  test("Parsing check-sat-assuming commands") {
    assert(parseUniqueCmd("(check-sat-assuming (a b c))") === 
           CheckSatAssuming(Seq(
             PropLiteral("a", true),
             PropLiteral("b", true),
             PropLiteral("c", true))))
    assert(parseUniqueCmd("(check-sat-assuming ((not a) b (not c)))") === 
           CheckSatAssuming(Seq(
             PropLiteral("a", false),
             PropLiteral("b", true),
             PropLiteral("c", false))))
  }

  test("Parsing declare-const commands") {
    assert(parseUniqueCmd("(declare-const a A)") ===
           DeclareConst(SSymbol("a"), Sort("A")))
    assert(parseUniqueCmd("(declare-const comp (A B))") ===
           DeclareConst(SSymbol("comp"), Sort("A", Seq(Sort("B")))))
    assert(parseUniqueCmd("(declare-const b (_ A 32))") ===
           DeclareConst(SSymbol("b"), Sort(Identifier("A", Seq(32)))))
  }


  test("Parsing declare-fun commands") {
    assert(parseUniqueCmd("(declare-fun xyz (A B) C)") ===
           DeclareFun("xyz", Seq(Sort("A"), Sort("B")), Sort("C")))
    assert(parseUniqueCmd("(declare-fun xyz () C)") ===
           DeclareFun("xyz", Seq(), Sort("C")))
    assert(parseUniqueCmd("(declare-fun xyz (A B) (C D))") ===
           DeclareFun("xyz", Seq(Sort("A"), Sort("B")), Sort("C", Seq(Sort("D")))))
  }

  test("Parsing declare-sort commands") {
    assert(parseUniqueCmd("(declare-sort A 0)") === DeclareSort("A", 0))
    assert(parseUniqueCmd("(declare-sort A 3)") === DeclareSort("A", 3))
  }


  test("Parsing define-fun commands") {
    assert(parseUniqueCmd("(define-fun f ((a A)) B a)") ===
           DefineFun(FunDef("f", Seq(SortedVar("a", Sort("A"))), Sort("B"), QualifiedIdentifier("a"))))
    assert(parseUniqueCmd("(define-fun f ((a A)) B (f a))") ===
           DefineFun(FunDef("f", Seq(SortedVar("a", Sort("A"))), Sort("B"),
                     FunctionApplication(QualifiedIdentifier("f"), Seq(QualifiedIdentifier("a"))))))
  }

  test("Parsing define-fun-rec commands") {
    assert(parseUniqueCmd("(define-fun-rec f ((a A)) B a)") ===
           DefineFunRec(FunDef("f", Seq(SortedVar("a", Sort("A"))), Sort("B"), QualifiedIdentifier("a"))))
    assert(parseUniqueCmd("(define-fun-rec f ((a A)) B (f a))") ===
           DefineFunRec(FunDef("f", Seq(SortedVar("a", Sort("A"))), Sort("B"),
                        FunctionApplication(QualifiedIdentifier("f"), Seq(QualifiedIdentifier("a"))))))
    assert(parseUniqueCmd("(define-fun-rec f ((a A)) A (f a))") ===
           DefineFunRec(FunDef("f", Seq(SortedVar("a", Sort("A"))), Sort("A"), 
                        FunctionApplication(QualifiedIdentifier("f"), Seq(QualifiedIdentifier("a"))))))

  }

  test("Parsing define-funs-rec commands") {
    assert(parseUniqueCmd(
"""(define-funs-rec
      ( (f ((a A)) B) (g ((a A)) B) )
      ( (g a) (f a) )
)""") ===
        DefineFunsRec(
          Seq(FunDec("f", Seq(SortedVar("a", Sort("A"))), Sort("B")),
              FunDec("g", Seq(SortedVar("a", Sort("A"))), Sort("B"))),
          Seq(FunctionApplication(QualifiedIdentifier("g"), Seq(QualifiedIdentifier("a"))),
              FunctionApplication(QualifiedIdentifier("f"), Seq(QualifiedIdentifier("a"))))
        )
    )
  }

  test("Parsing define-sort commands") {
    assert(parseUniqueCmd("(define-sort A () B)") ===
           DefineSort("A", Seq(), Sort("B")))
    assert(parseUniqueCmd("(define-sort A (B C) (Array B C))") ===
           DefineSort("A", Seq("B", "C"), 
                      Sort(Identifier("Array"), 
                           Seq(Sort("B"), Sort("C")))))
  }

  test("Parsing echo commands") {
    assert(parseUniqueCmd("""(echo "abcd")""") === Echo(SString("abcd")))
    assert(parseUniqueCmd("""(echo "alpha")""") === Echo(SString("alpha")))
  }
  test("Parsing exit command") {
    assert(parseUniqueCmd("(exit)") === Exit())
  }

  test("Parsing get-assertions command") {
    assert(parseUniqueCmd("(get-assertions)") === GetAssertions())
  }
  test("Parsing get-assignment command") {
    assert(parseUniqueCmd("(get-assignment)") === GetAssignment())
  }

  test("Parsing get-info commands") {
    assert(parseUniqueCmd("(get-info :all-statistics)") === GetInfo(AllStatisticsInfoFlag()))
    assert(parseUniqueCmd("(get-info :assertion-stack-levels)") === GetInfo(AssertionStackLevelsInfoFlag()))
    assert(parseUniqueCmd("(get-info :authors)") === GetInfo(AuthorsInfoFlag()))
    assert(parseUniqueCmd("(get-info :error-behavior)") === GetInfo(ErrorBehaviorInfoFlag()))
    assert(parseUniqueCmd("(get-info :name)") === GetInfo(NameInfoFlag()))
    assert(parseUniqueCmd("(get-info :reason-unknown)") === GetInfo(ReasonUnknownInfoFlag()))
    assert(parseUniqueCmd("(get-info :version)") === GetInfo(VersionInfoFlag()))
    assert(parseUniqueCmd("(get-info :custom)") === GetInfo(KeywordInfoFlag("custom")))
  }

  test("Parsing get-model command") {
    assert(parseUniqueCmd("(get-model)") === GetModel())
  }

  test("Parsing get-option commands") {
    assert(parseUniqueCmd("(get-option :keyword)") === GetOption("keyword"))
    assert(parseUniqueCmd("(get-option :custom)") === GetOption("custom"))
  }

  test("Parsing get-proof command") {
    assert(parseUniqueCmd("(get-proof)") === GetProof())
  }
  test("Parsing get-unsat-assumptions command") {
    assert(parseUniqueCmd("(get-unsat-assumptions)") === GetUnsatAssumptions())
  }
  test("Parsing get-unsat-core command") {
    assert(parseUniqueCmd("(get-unsat-core)") === GetUnsatCore())
  }

  test("Parsing get-value commands") {
    assert(parseUniqueCmd("(get-value (x y z))") === GetValue(SSymbol("x"), Seq(SSymbol("y"), SSymbol("z"))))
  }

  //TODO
  //test("get-value expects at least one term") {
  //  intercept[UnexpectedTokenException] {
  //    parseUniqueCmd("(get-value ())")
  //  }
  //}

  test("Parsing pop commands") {
    assert(parseUniqueCmd("(pop 1)") === Pop(1))
    assert(parseUniqueCmd("(pop 2)") === Pop(2))
  }
  test("Parsing push commands") {
    assert(parseUniqueCmd("(push 1)") === Push(1))
    assert(parseUniqueCmd("(push 4)") === Push(4))
  }

  test("Parsing reset command") {
    assert(parseUniqueCmd("(reset)") === Reset())
  }
  test("Parsing reset-assertions command") {
    assert(parseUniqueCmd("(reset-assertions)") === ResetAssertions())
  }

  test("Parsing set-info command") {
    assert(parseUniqueCmd("""(set-info :author "Reg")""") === SetInfo(Attribute(SKeyword("author"), Some(SString("Reg")))))
    assert(parseUniqueCmd("""(set-info :number 42)""") === SetInfo(Attribute(SKeyword("number"), Some(SNumeral(42)))))
    assert(parseUniqueCmd("""(set-info :test)""") === SetInfo(Attribute(SKeyword("test"), None)))
  }

  test("Parsing the different set-logic commands") {
    assert(parseUniqueCmd("(set-logic AUFLIA)")  === SetLogic(AUFLIA()))
    assert(parseUniqueCmd("(set-logic AUFLIRA)")  === SetLogic(AUFLIRA()))
    assert(parseUniqueCmd("(set-logic AUFNIRA)")  === SetLogic(AUFNIRA()))
    assert(parseUniqueCmd("(set-logic LRA)")  === SetLogic(LRA()))

    assert(parseUniqueCmd("(set-logic QF_ABV)")  === SetLogic(QF_ABV()))
    assert(parseUniqueCmd("(set-logic QF_AUFBV)")  === SetLogic(QF_AUFBV()))
    assert(parseUniqueCmd("(set-logic QF_AUFLIA)")  === SetLogic(QF_AUFLIA()))
    assert(parseUniqueCmd("(set-logic QF_AX)")  === SetLogic(QF_AX()))
    assert(parseUniqueCmd("(set-logic QF_BV)")  === SetLogic(QF_BV()))
    assert(parseUniqueCmd("(set-logic QF_IDL)")  === SetLogic(QF_IDL()))
    assert(parseUniqueCmd("(set-logic QF_LIA)") === SetLogic(QF_LIA()))
    assert(parseUniqueCmd("(set-logic QF_LRA)") === SetLogic(QF_LRA()))
    assert(parseUniqueCmd("(set-logic QF_NIA)") === SetLogic(QF_NIA()))
    assert(parseUniqueCmd("(set-logic QF_NRA)") === SetLogic(QF_NRA()))
    assert(parseUniqueCmd("(set-logic QF_RDL)") === SetLogic(QF_RDL()))
    assert(parseUniqueCmd("(set-logic QF_UF)")  === SetLogic(QF_UF()))
    assert(parseUniqueCmd("(set-logic QF_UFBV)")  === SetLogic(QF_UFBV()))
    assert(parseUniqueCmd("(set-logic QF_UFIDL)")  === SetLogic(QF_UFIDL()))
    assert(parseUniqueCmd("(set-logic QF_UFLIA)")  === SetLogic(QF_UFLIA()))
    assert(parseUniqueCmd("(set-logic QF_UFLRA)")  === SetLogic(QF_UFLRA()))
    assert(parseUniqueCmd("(set-logic QF_UFNRA)")  === SetLogic(QF_UFNRA()))

    assert(parseUniqueCmd("(set-logic UFLRA)")  === SetLogic(UFLRA()))
    assert(parseUniqueCmd("(set-logic UFNIA)")  === SetLogic(UFNIA()))
  }

  test("Parsing set-logic all command") {
    assert(parseUniqueCmd("(set-logic ALL)") === SetLogic(ALL()))
  }

  test("Parsing non standard set-logic commands") {
    assert(parseUniqueCmd("(set-logic UNIQUE_LOGIC)") === 
      SetLogic(NonStandardLogic(SSymbol("UNIQUE_LOGIC"))))
    assert(parseUniqueCmd("(set-logic MY_COOL_LOGIC)") === 
      SetLogic(NonStandardLogic(SSymbol("MY_COOL_LOGIC"))))
  }

  test("Parsing set-option command") {
    assert(parseUniqueCmd("""(set-option :diagnostic-output-channel "toto")""") === 

                          SetOption(DiagnosticOutputChannel("toto")))
    assert(parseUniqueCmd("(set-option :global-declarations true)") === SetOption(GlobalDeclarations(true)))
    assert(parseUniqueCmd("(set-option :global-declarations false)") === SetOption(GlobalDeclarations(false)))

    assert(parseUniqueCmd("(set-option :interactive-mode true)") === SetOption(InteractiveMode(true)))
    assert(parseUniqueCmd("(set-option :interactive-mode false)") === SetOption(InteractiveMode(false)))

    assert(parseUniqueCmd("(set-option :print-success true)") === SetOption(PrintSuccess(true)))
    assert(parseUniqueCmd("(set-option :print-success false)") === SetOption(PrintSuccess(false)))

    assert(parseUniqueCmd("(set-option :produce-assertions true)") === SetOption(ProduceAssertions(true)))
    assert(parseUniqueCmd("(set-option :produce-assertions false)") === SetOption(ProduceAssertions(false)))
    assert(parseUniqueCmd("(set-option :produce-assignments true)") === SetOption(ProduceAssignments(true)))
    assert(parseUniqueCmd("(set-option :produce-assignments false)") === SetOption(ProduceAssignments(false)))
    assert(parseUniqueCmd("(set-option :produce-models true)") === SetOption(ProduceModels(true)))
    assert(parseUniqueCmd("(set-option :produce-models false)") === SetOption(ProduceModels(false)))
    assert(parseUniqueCmd("(set-option :produce-proofs true)") === SetOption(ProduceProofs(true)))
    assert(parseUniqueCmd("(set-option :produce-proofs false)") === SetOption(ProduceProofs(false)))
    assert(parseUniqueCmd("(set-option :produce-unsat-assumptions true)") === SetOption(ProduceUnsatAssumptions(true)))
    assert(parseUniqueCmd("(set-option :produce-unsat-assumptions false)") === SetOption(ProduceUnsatAssumptions(false)))
    assert(parseUniqueCmd("(set-option :produce-unsat-cores true)") === SetOption(ProduceUnsatCores(true)))
    assert(parseUniqueCmd("(set-option :produce-unsat-cores false)") === SetOption(ProduceUnsatCores(false)))

    assert(parseUniqueCmd("(set-option :random-seed 42)") === SetOption(RandomSeed(42)))
    assert(parseUniqueCmd("(set-option :random-seed 12)") === SetOption(RandomSeed(12)))

    assert(parseUniqueCmd("""(set-option :regular-output-channel "test")""") === 
                          SetOption(RegularOutputChannel("test")))

    assert(parseUniqueCmd("(set-option :reproducible-resource-limit 4)") === SetOption(ReproducibleResourceLimit(4)))
    assert(parseUniqueCmd("(set-option :reproducible-resource-limit 1)") === SetOption(ReproducibleResourceLimit(1)))
    assert(parseUniqueCmd("(set-option :verbosity 4)") === SetOption(Verbosity(4)))
    assert(parseUniqueCmd("(set-option :verbosity 1)") === SetOption(Verbosity(1)))

    assert(parseUniqueCmd("(set-option :custom 42)") === SetOption(AttributeOption(
      Attribute(SKeyword("custom"), Some(SNumeral(42))))))
    assert(parseUniqueCmd("(set-option :my-option)") === SetOption(AttributeOption(
      Attribute(SKeyword("my-option"), None))))
    assert(parseUniqueCmd("""(set-option :custom "abcd")""") === SetOption(AttributeOption(
      Attribute(SKeyword("custom"), Some(SString("abcd"))))))
    assert(parseUniqueCmd("""(set-option :custom-flag true)""") === SetOption(AttributeOption(
      Attribute(SKeyword("custom-flag"), Some(SSymbol("true"))))))
    assert(parseUniqueCmd("""(set-option :custom-flag false)""") === SetOption(AttributeOption(
      Attribute(SKeyword("custom-flag"), Some(SSymbol("false"))))))
  }

  test("Attribute value cannot be a kewyord. Should throw UnexpectedTokenException") {
    intercept[UnexpectedTokenException] {
      parseUniqueCmd("""(set-option :custom :abcd)""")
    }
  }

  test("Parsing unknown command throws UnknownCommandException") {
    val reader1 = new StringReader("(alpha beta)")
    val lexer1 = new Lexer(reader1)
    val parser1 = new Parser(lexer1)
    intercept[UnknownCommandException] {
      parser1.parseCommand
    }
  }


  test("Parsing declare-datatypes commands") {
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

  test("Commands with terms have correct positions") {
    val cmd3 = parseUniqueCmd("(assert (< x y))")
    assert(cmd3.getPos === Position(1, 1))
    val Assert(fa@FunctionApplication(fun, Seq(x, y))) = cmd3
    assert(fa.getPos === Position(1, 9))
    assert(fun.getPos === Position(1, 10))
    assert(x.getPos === Position(1, 12))
    assert(y.getPos === Position(1, 14))

    {
      val cmd4 = parseUniqueCmd("(get-value (x y z))")
      val GetValue(x, Seq(y, z)) = cmd4
      assert(cmd4.getPos === Position(1,1))
      assert(x.getPos === Position(1,13))
      assert(y.getPos === Position(1,15))
      assert(z.getPos === Position(1,17))
    }
  }

  test("Commands without arguments have correct positions") {
    assert(parseUniqueCmd("(check-sat)").getPos === Position(1,1))
    assert(parseUniqueCmd("(exit)").getPos === Position(1,1))
    assert(parseUniqueCmd("(get-assertions)").getPos === Position(1,1))
    assert(parseUniqueCmd("(get-assignment)").getPos === Position(1,1))
    assert(parseUniqueCmd("(get-proof)").getPos === Position(1,1))
    assert(parseUniqueCmd("(get-unsat-assumptions)").getPos === Position(1,1))
    assert(parseUniqueCmd("(get-unsat-core)").getPos === Position(1,1))
    assert(parseUniqueCmd("(reset)").getPos === Position(1,1))
    assert(parseUniqueCmd("(reset-assertions)").getPos === Position(1,1))
  }

  test("Commands with simple flat structure have correct positions") {
    val cmd1 = parseUniqueCmd("""(echo "Hello World")""")
    val Echo(hello) = cmd1
    assert(cmd1.getPos === Position(1,1))
    assert(hello.getPos === Position(1,7))

    val cmd2 = parseUniqueCmd("""(check-sat-assuming ((not a) b (not c)))""")
    val CheckSatAssuming(Seq(l1, l2, l3)) = cmd2
    assert(cmd2.getPos === Position(1,1))
    assert(l1.getPos === Position(1,22))
    assert(l2.getPos === Position(1,30))
    assert(l3.getPos === Position(1,32))
  }

  test("Commands for declarations and definitions have correct positions") {
    {
      val declareConst = parseUniqueCmd("(declare-const a A)")
      val DeclareConst(a, sa) = declareConst
      assert(declareConst.getPos === Position(1,1))
      assert(a.getPos === Position(1,16))
      assert(sa.getPos === Position(1, 18))
    }

    {
      val declareFun = parseUniqueCmd("(declare-fun f (A B) C)")
      val DeclareFun(f, Seq(a,b), c) = declareFun
      assert(declareFun.getPos === Position(1,1))
      assert(f.getPos === Position(1,14))
      assert(a.getPos === Position(1,17))
      assert(b.getPos === Position(1,19))
      assert(c.getPos === Position(1,22))
    }

    {
      val declareSort = parseUniqueCmd("(declare-sort A 3)")
    assert(parseUniqueCmd("(declare-sort A 3)") === DeclareSort("A", 3))
      val DeclareSort(a, n) = declareSort
      assert(declareSort.getPos === Position(1,1))
      assert(a.getPos === Position(1,15))
    }

    {
      val defineFun = parseUniqueCmd("(define-fun f ((a A)) B a)")
      val DefineFun(FunDef(f, Seq(a), b, ta)) = defineFun
      assert(defineFun.getPos === Position(1,1))
      assert(f.getPos === Position(1,13))
      assert(a.getPos === Position(1,16))
      assert(b.getPos === Position(1,23))
      assert(ta.getPos === Position(1,25))
    }

    {
      val defineSort = parseUniqueCmd("(define-sort A () B)")
      val DefineSort(a, Seq(), b) = defineSort
      assert(defineSort.getPos === Position(1,1))
      assert(a.getPos === Position(1,14))
      assert(b.getPos === Position(1,19))
    }
  }

  test("Info have correct positions") {
    val setInfo1 = parseUniqueCmd("""(set-info :author "Reg")""")
    val SetInfo(attr@Attribute(author, Some(reg))) = setInfo1
    assert(setInfo1.getPos === Position(1, 1))
    assert(attr.getPos === Position(1, 11))
    assert(author.getPos === Position(1, 11))
    assert(reg.getPos === Position(1, 19))

    assert(parseUniqueCmd("""(set-info :test)""") === SetInfo(Attribute(SKeyword("test"), None)))
    val setInfo2 = parseUniqueCmd("(set-info :test)")
    val SetInfo(attr2@Attribute(test, None)) = setInfo2
    assert(setInfo2.getPos === Position(1, 1))
    assert(attr2.getPos === Position(1, 11))
    assert(test.getPos === Position(1, 11))

    val getInfo1 = parseUniqueCmd("(get-info :all-statistics)")
    val GetInfo(flag1) = getInfo1
    assert(getInfo1.getPos === Position(1, 1))
    assert(flag1.getPos === Position(1, 11))

    val getInfo2 = parseUniqueCmd("(get-info :authors)")
    val GetInfo(flag2) = getInfo2
    assert(getInfo2.getPos === Position(1, 1))
    assert(flag2.getPos === Position(1, 11))

    //that one is different as we are parsing a custom info flag, and not a built-in
    val getInfo3 = parseUniqueCmd("(get-info :custom)")
    val GetInfo(flag3) = getInfo3
    assert(getInfo3.getPos === Position(1, 1))
    assert(flag3.getPos === Position(1, 11))
  }

  test("Logics have correct positions") {
    val setLogic1 = parseUniqueCmd("(set-logic AUFLIA)")
    val SetLogic(logic1) = setLogic1
    assert(setLogic1.getPos === Position(1,1))
    assert(logic1.getPos === Position(1, 12))

    val setLogic2 = parseUniqueCmd("(set-logic LRA)")
    val SetLogic(logic2) = setLogic2
    assert(setLogic2.getPos === Position(1,1))
    assert(logic2.getPos === Position(1, 12))

    val setLogic3 = parseUniqueCmd("(set-logic ALL)")
    val SetLogic(logic3) = setLogic3
    assert(setLogic3.getPos === Position(1,1))
    assert(logic3.getPos === Position(1, 12))

    val setLogic4 = parseUniqueCmd("(set-logic UNIQUE_LOGIC)")
    val SetLogic(logic4@NonStandardLogic(customLogicSym)) = setLogic4
    assert(setLogic4.getPos === Position(1,1))
    assert(logic4.getPos === Position(1, 12))
    assert(customLogicSym.getPos === Position(1, 12))
  }

  test("Options have correct positions") {
    def assertOptionPosition(raw: String, pos: Position): Unit = {
      val SetOption(option) = parseUniqueCmd(raw)
      assert(option.getPos === pos)
    }

    assertOptionPosition("""(set-option :diagnostic-output-channel "toto")""", Position(1, 13))
    assertOptionPosition("(set-option :global-declarations true)", Position(1, 13))
    assertOptionPosition("(set-option :interactive-mode true)", Position(1, 13))
    assertOptionPosition("(set-option :print-success true)", Position(1, 13))
    assertOptionPosition(" (set-option  :print-success false)", Position(1, 15))
    assertOptionPosition("(set-option :produce-assertions true)", Position(1, 13))
    assertOptionPosition("(set-option :produce-assignments true)", Position(1, 13))
    assertOptionPosition("(set-option :random-seed 42)", Position(1, 13))
    assertOptionPosition("""(set-option :regular-output-channel "test")""", Position(1, 13))

    val customOptionCmd = parseUniqueCmd("(set-option :custom 42)")
    val SetOption(attr@AttributeOption(Attribute(keyword, Some(numeral)))) = customOptionCmd
    assert(customOptionCmd.getPos === Position(1, 1))
    assert(attr.getPos === Position(1, 13))
    assert(keyword.getPos === Position(1, 13))

    val getOptionCmd = parseUniqueCmd("(get-option :keyword)")
    val GetOption(keyword2) = getOptionCmd
    assert(getOptionCmd.getPos === Position(1, 1))
    assert(keyword2.getPos === Position(1, 13))
  }

  test("Commands over multiple lines have correct positions") {
    val script =
"""(get-assertions)
(check-sat)
(exit)"""

    val reader = new StringReader(script)
    val lexer = new Lexer(reader)
    val parser = new Parser(lexer)
    val cmd1 = parser.parseCommand
    val cmd2 = parser.parseCommand
    val cmd3 = parser.parseCommand
    assert(lexer.nextToken == null)
    assert(cmd1.getPos === Position(1,1))
    assert(cmd2.getPos === Position(2,1))
    assert(cmd3.getPos === Position(3,1))
  }

  //TODO: sort position tests, maybe need to introduce a ParseCommon object


  private def assertEachNodeHasPos(t: Tree): Unit = {
    TreesOps.foreach((t: Tree) => assert(t.hasPos, "node [" + t + "] does not have a position"))(t)
  }
}
