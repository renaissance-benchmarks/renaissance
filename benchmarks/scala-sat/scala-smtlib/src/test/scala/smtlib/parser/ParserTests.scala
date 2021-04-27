package smtlib
package parser

import lexer._
import common._
import Parser._
import trees.Tree
import trees.Commands._
import trees.Terms._
import trees.TreesOps

import java.io.StringReader

import org.scalatest.concurrent.TimeLimits
import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.time.SpanSugar._

import scala.language.implicitConversions

class ParserTests extends AnyFunSuite with TimeLimits {

  override def suiteName = "SMT-LIB Parser suite"

  def parseUniqueTerm(str: String): Term = {
    val reader = new StringReader(str)
    val lexer = new Lexer(reader)
    val parser = new Parser(lexer)
    val term = parser.parseTerm
    assert(lexer.nextToken == null)
    assertEachNodeHasPos(term)
    term
  }

  def parseUniqueSExpr(str: String): SExpr = {
    val reader = new StringReader(str)
    val lexer = new Lexer(reader)
    val parser = new Parser(lexer)
    val sexpr = parser.parseSExpr
    assert(lexer.nextToken == null)
    sexpr
  }

  private implicit def strToSym(str: String): SSymbol = SSymbol(str)
  private implicit def strToId(str: String): Identifier = Identifier(SSymbol(str))
  private implicit def strToKeyword(str: String): SKeyword = SKeyword(str)
  private implicit def symToTerm(sym: SSymbol): QualifiedIdentifier = QualifiedIdentifier(sym.name)
  private implicit def intToNum(n: Int): SNumeral = SNumeral(n)
  private implicit def IntSeqToIndices(ns: Seq[Int]): Seq[Index] = ns.map(n => SNumeral(n))


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
    assert(parseId("(_ a sym)") === Identifier("a", Seq(SSymbol("sym"))))
    assert(parseId("(_ map f)") === Identifier("map", Seq(SSymbol(("f")))))
  }

  ignore("parsing magical lambda terms form CVC4") {
    val t = parseUniqueTerm("(LAMBDA ((_ufmt_1 Int)) (ite (= _ufmt_1 2) 3 5))")
    println(t)
  }

  test("comments are ignored after a term") {
    assert(parseUniqueTerm("42 ;I'm a comment") === SNumeral(42))
    assert(parseUniqueTerm("42;I'm another comment") === SNumeral(42))
  }

  test("Literal/constant terms are parsed correctly") {
    assert(parseUniqueTerm("42") === SNumeral(42))
    assert(parseUniqueTerm("42.12") === SDecimal(42.12))
    assert(parseUniqueTerm("#xF") === SHexadecimal(Hexadecimal.fromString("F").get))
    assert(parseUniqueTerm("#b1") === SBinary(List(true)))
    assert(parseUniqueTerm(" \"Hey there\" ") === SString("Hey there"))
  }

  test("semicolon as part of string literal does not start a comment") {
    assert(parseUniqueTerm(" \"Hey ;there\" ") === SString("Hey ;there"))
  }

  test("Correctly parsing identifier and qualfieid identifiers terms") {
    assert(parseUniqueTerm("abc") === QualifiedIdentifier("abc"))
    assert(parseUniqueTerm("eee") === QualifiedIdentifier("eee"))

    assert(parseUniqueTerm("(_ abc 42)") === QualifiedIdentifier(Identifier("abc", Seq(42))))
    assert(parseUniqueTerm("(_ efg 12)") === QualifiedIdentifier(Identifier("efg", Seq(12))))
  }

  test("Correctly parsing as-identifier terms") {
    assert(parseUniqueTerm("(as abc A)") === QualifiedIdentifier("abc", Some(Sort("A"))))
    assert(parseUniqueTerm("(as aaaa AB)") === QualifiedIdentifier("aaaa", Some(Sort("AB"))))
    assert(parseUniqueTerm("(as aaaa (A B C))") === QualifiedIdentifier("aaaa", Some(Sort("A", Seq(Sort("B"), Sort("C"))))))
  }


  test("Test weird syntax combination of as/_ for identifier") {
    assert(parseUniqueTerm("(as (_ abc 42) A)") === QualifiedIdentifier(Identifier("abc", Seq(42)), Some(Sort("A"))))
  }

  test("Parsing function applications") {
    assert(parseUniqueTerm("(f a b)") === 
           FunctionApplication(
            QualifiedIdentifier("f"), Seq(QualifiedIdentifier("a"), QualifiedIdentifier("b"))))

    assert(parseUniqueTerm("(f (g a b) c)") === 
           FunctionApplication(
            QualifiedIdentifier("f"), Seq(
              FunctionApplication(
                QualifiedIdentifier("g"), 
                Seq(QualifiedIdentifier("a"), QualifiedIdentifier("b"))
              ),
              QualifiedIdentifier("c"))))
  }

  test("Parsing Let bindings terms") {
    assert(parseUniqueTerm("(let ((a x)) 42)") ===
           Let(VarBinding("a", QualifiedIdentifier("x")), Seq(), SNumeral(42)))

    assert(parseUniqueTerm("(let ((a x)) a)") ===
           Let(VarBinding("a", QualifiedIdentifier("x")), Seq(), QualifiedIdentifier("a")))

    assert(parseUniqueTerm("(let ((a x) (b y)) (f a b))") ===
           Let(VarBinding("a", QualifiedIdentifier("x")), 
               Seq(VarBinding("b", QualifiedIdentifier("y"))), 
               FunctionApplication(QualifiedIdentifier("f"),
                Seq(QualifiedIdentifier("a"), QualifiedIdentifier("b")))))
  }

  test("Let bindings with no binding throws unexpected token exception") {
    intercept[UnexpectedTokenException] {
      parseUniqueTerm("(let () 42)")
    }
  }

  test("Let bindings with missing closing parenthesis in binding throws unexpected token exception") {
    intercept[UnexpectedTokenException] {
      parseUniqueTerm("(let ((a 2) a)")
    }
  }

  test("Let with binding to complex term works as expected") {
    assert(parseUniqueTerm("(let ((a (f x y))) 42)") ===
           Let(
            VarBinding("a", 
              FunctionApplication(QualifiedIdentifier("f"),
                                  Seq(QualifiedIdentifier("x"), 
                                      QualifiedIdentifier("y")))),
            Seq(),
            SNumeral(42)))
  }


  test("Parsing quantified terms") {
    assert(parseUniqueTerm("(forall ((a A)) a)") ===
           Forall(SortedVar("a", Sort("A")), Seq(), QualifiedIdentifier("a"))
          )
    assert(parseUniqueTerm("(forall ((a A) (b B) (c C)) (f a c))") ===
           Forall(SortedVar("a", Sort("A")), 
                  Seq(SortedVar("b", Sort("B")), SortedVar("c", Sort("C"))),
                  FunctionApplication(QualifiedIdentifier("f"),
                    Seq(QualifiedIdentifier("a"), QualifiedIdentifier("c")))))

    assert(parseUniqueTerm("(exists ((a A)) a)") ===
           Exists(SortedVar("a", Sort("A")), Seq(), QualifiedIdentifier("a"))
          )
    assert(parseUniqueTerm("(exists ((a A) (b B) (c C)) (f a c))") ===
           Exists(SortedVar("a", Sort("A")), 
                  Seq(SortedVar("b", Sort("B")), SortedVar("c", Sort("C"))),
                  FunctionApplication(QualifiedIdentifier("f"),
                    Seq(QualifiedIdentifier("a"), QualifiedIdentifier("c")))))
  }

  test("quantified terms with no binding throws unexpected token exception") {
    intercept[UnexpectedTokenException] {
      parseUniqueTerm("(forall () true)")
    }
    intercept[UnexpectedTokenException] {
      parseUniqueTerm("(exists () true)")
    }
  }

  test("Parsing annotated term") {
    assert(parseUniqueTerm("(! a :note abcd)") ===
           AnnotatedTerm(QualifiedIdentifier("a"), Attribute(SKeyword("note"), Some(SSymbol("abcd"))), Seq())
          )
    assert(parseUniqueTerm("(! (f a) :note abcd)") ===
           AnnotatedTerm(
            FunctionApplication(QualifiedIdentifier("f"), Seq(QualifiedIdentifier("a"))), 
            Attribute(SKeyword("note"), Some(SSymbol("abcd"))), Seq())
          )

  }

  test("Annotated terms with zero annotation throws unexpected token exception") {
    intercept[UnexpectedTokenException] {
      parseUniqueTerm("(! a)")
    }
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

  test("Parsing FunctionApplication without closing parentheses should throw UnexpectedEOFException") {
    intercept[UnexpectedEOFException] {
      parseUniqueTerm("(f a b")
    }
    intercept[UnexpectedEOFException] {
      parseUniqueTerm("(f a (g b)") //more subtle
    }
  }

  test("Parsing FunctionApplication without argument should throw UnexpectedTokenException") {
    intercept[UnexpectedTokenException] {
      parseUniqueTerm("(f)")
    }
    intercept[UnexpectedTokenException] {
      parseUniqueTerm("(abcd)")
    }
  }

  test("Parsing terms with eof in middle should throw UnexpectedEOFException") {
    intercept[UnexpectedEOFException] {
      parseUniqueTerm("")
    }
    intercept[UnexpectedEOFException] {
      parseUniqueTerm("(")
    }
    intercept[UnexpectedEOFException] {
      parseUniqueTerm("(let")
    }
    intercept[UnexpectedEOFException] {
      parseUniqueTerm("(let ((x t))")
    }
  }

  test("Parsing s-expressions") {
    assert(parseUniqueSExpr("42") === SNumeral(42))
    assert(parseUniqueSExpr("12.38") === SDecimal(12.38))
    assert(parseUniqueSExpr("#xa1f") === SHexadecimal(Hexadecimal.fromString("a1f").get))
    assert(parseUniqueSExpr("#b1010") === SBinary(List(true, false, true, false)))
    assert(parseUniqueSExpr(""" "hey there" """) === SString("hey there"))
    assert(parseUniqueSExpr("abcd") === SSymbol("abcd"))
    assert(parseUniqueSExpr(":abcd") === SKeyword("abcd"))
    assert(parseUniqueSExpr("(abc def 42)") === 
      SList(SSymbol("abc"), SSymbol("def"), SNumeral(42)))
  }

  test("s-expression list can be empty") {
    assert(parseUniqueSExpr("()") === SList())
  }

  test("s-expression can parse reserved words as symbols") {
    assert(parseUniqueSExpr("(set-logic QF_BV)") === SList(SSymbol("set-logic"), SSymbol("QF_BV")))
    assert(parseUniqueSExpr("(declare-const)") === SList(SSymbol("declare-const")))
    assert(parseUniqueSExpr("check-sat") === SSymbol("check-sat"))
  }

  test("eof in middle of s-list should throw UnexpectedEOFException") {
    intercept[UnexpectedEOFException] {
      parseUniqueSExpr("")
    }
    intercept[UnexpectedEOFException] {
      parseUniqueSExpr("(a b")
    }
  }

  test("simple benchmark") {
    val benchmark = """
      (set-logic QF_UF)
      (declare-fun f (Int) Int)
      (declare-fun a () Int)
      (assert (= (f a) a))
      (check-sat)
    """
    val cmd1 = SetLogic(QF_UF())
    val cmd2 = DeclareFun("f", Seq(Sort("Int")), Sort("Int"))
    val cmd3 = DeclareFun("a", Seq(), Sort("Int"))
    val cmd4 =
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
    val cmd5 = CheckSat()

    val reader1 = new StringReader(benchmark)
    val lexer1 = new Lexer(reader1)
    val parser1 = new Parser(lexer1)
    assert(parser1.parseCommand === cmd1)
    assert(parser1.parseCommand === cmd2)
    assert(parser1.parseCommand === cmd3)
    assert(parser1.parseCommand === cmd4)
    assert(parser1.parseCommand === cmd5)

    val reader2 = new StringReader(benchmark)
    val lexer2 = new Lexer(reader2)
    val parser2 = new Parser(lexer2)
    assert(parser2.parseScript === Script(List(cmd1, cmd2, cmd3, cmd4, cmd5)))
  }

  test("interactive parser") {
    val pis = new SynchronousPipedReader
    val lexer = failAfter(3 seconds) { new Lexer(pis) }
    val parser = failAfter(3 seconds) { new Parser(lexer) }

    pis.write("(set-logic QF_LRA)")
    assert(parser.parseCommand === SetLogic(QF_LRA()))

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

  test("identifiers object helpers work") {
    val abc = SSymbol("abc")
    val ext = SSymbol("def")

    val simpleId = SimpleIdentifier(abc)
    assert(simpleId === Identifier(abc))
    simpleId match {
      case SimpleIdentifier(sym) => assert(sym === abc)
      case _ => assert(false)
    }
    simpleId match {
      case ExtendedIdentifier(sym, ext) => assert(false)
      case SimpleIdentifier(sym) => assert(sym === abc)
      case _ => assert(false)
    }

    val extId = ExtendedIdentifier(abc, ext)
    assert(extId === Identifier(abc, Seq(ext)))
    extId match {
      case ExtendedIdentifier(a, b) => 
        assert(a === abc)
        assert(b === ext)
      case _ => ???
    }
    extId match {
      case SimpleIdentifier(sym) => assert(false)
      case ExtendedIdentifier(a, b) => 
        assert(a === abc)
        assert(b === ext)
      case _ => ???
    }

  }

  private def assertEachNodeHasPos(t: Tree): Unit = {
    TreesOps.foreach((t: Tree) => assert(t.hasPos, "node [" + t + "] does not have a position"))(t)
  }

}
