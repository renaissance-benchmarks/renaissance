package smtlib
package lexer

import Tokens._
import common._

import java.io.StringReader

import org.scalatest.FunSuite
import org.scalatest.concurrent.Timeouts
import org.scalatest.time.SpanSugar._

class LexerTests extends FunSuite with Timeouts {

  override def suiteName = "Lexer Test Suite"

  //parse the string for a single command and asserts no more commands
  private def lexUniqueToken(str: String): Token = {
    val reader = new StringReader(str)
    val lexer = new Lexer(reader)
    val token = lexer.nextToken
    assert(lexer.nextToken === null)
    token
  }

  test("eof read") {
    val reader1 = new StringReader("12")
    val lexer1 = new Lexer(reader1)
    assert(lexer1.nextToken === NumeralLit(12))
    assert(lexer1.nextToken === null)
  }

  test("ignoring comments") {
    assert(lexUniqueToken(""";blablablabla blabla 42
                             12
                          """) === NumeralLit(12))
    assert(lexUniqueToken(""";test
                             "13"
                             ;retest
                          """) === StringLit("13"))
    assert(lexUniqueToken("""14 ;retest""") === NumeralLit(14))
    assert(lexUniqueToken(""";this is a comment
                             15;this is a comment very close to the literal
                          """) === NumeralLit(15))
  }

  test("integer literals") {
    assert(lexUniqueToken("0") === NumeralLit(0))
    assert(lexUniqueToken("1") === NumeralLit(1))
    assert(lexUniqueToken("100") === NumeralLit(100))
    val reader1 = new StringReader("12")
    val lexer1 = new Lexer(reader1)
    assert(lexer1.nextToken === NumeralLit(12))

    assert(lexUniqueToken("#x0") === HexadecimalLit(Hexadecimal.fromString("0").get))
    val reader2 = new StringReader("#xF")
    val lexer2 = new Lexer(reader2)
    assert(lexer2.nextToken === HexadecimalLit(Hexadecimal.fromString("F").get))

    val reader3 = new StringReader("#x002a")
    val lexer3 = new Lexer(reader3)
    assert(lexer3.nextToken === HexadecimalLit(Hexadecimal.fromString("002A").get))

    val reader4 = new StringReader("#x1F")
    val lexer4 = new Lexer(reader4)
    assert(lexer4.nextToken === HexadecimalLit(Hexadecimal.fromString("1F").get))

    val reader5 = new StringReader("123 #x11 12")
    val lexer5 = new Lexer(reader5)
    assert(lexer5.nextToken === NumeralLit(123))
    assert(lexer5.nextToken === HexadecimalLit(Hexadecimal.fromString("11").get))
    assert(lexer5.nextToken === NumeralLit(12))

    assert(lexUniqueToken("#b0") === BinaryLit(Seq(false)))
    assert(lexUniqueToken("#b1") === BinaryLit(Seq(true)))
    assert(lexUniqueToken("#b001") === BinaryLit(Seq(false, false, true)))
    val reader6 = new StringReader("#b1010")
    val lexer6 = new Lexer(reader6)
    assert(lexer6.nextToken === BinaryLit(Seq(true, false, true, false)))
  }

  test("string literals") {
    val reader1 = new StringReader(""" "12" """)
    val lexer1 = new Lexer(reader1)
    assert(lexer1.nextToken === StringLit("12"))

    val reader2 = new StringReader(""" "abc\"def" """)
    val lexer2 = new Lexer(reader2)
    assert(lexer2.nextToken === StringLit("abc\"def"))

    val reader3 = new StringReader(""" " abc \" def" """)
    val lexer3 = new Lexer(reader3)
    assert(lexer3.nextToken === StringLit(" abc \" def"))

    val reader4 = new StringReader(""" "\"abc\"" """)
    val lexer4 = new Lexer(reader4)
    assert(lexer4.nextToken === StringLit("\"abc\""))

    assert(lexUniqueToken(""" "abc\ndef" """) === StringLit("""abc\ndef"""))
    assert(lexUniqueToken(""" "abc\n def" """) === StringLit("""abc\n def"""))
    assert(lexUniqueToken(""" "123\d456" """) === StringLit("""123\d456"""))

    assert(lexUniqueToken(""" "123\\456" """) === StringLit("""123\456"""))
    assert(lexUniqueToken(""" "test\\" """) === StringLit("""test\"""))
  }


  test("symbol literals") {
    val reader1 = new StringReader(""" d12 """)
    val lexer1 = new Lexer(reader1)
    assert(lexer1.nextToken === SymbolLit("d12"))

    val reader2 = new StringReader(""" abc\ def """)
    val lexer2 = new Lexer(reader2)
    assert(lexer2.nextToken === SymbolLit("abc def"))

    val reader3 = new StringReader("""  ab\c\ d\ef" """)
    val lexer3 = new Lexer(reader3)
    assert(lexer3.nextToken === SymbolLit("abc def"))

    val reader4 = new StringReader(""" |abc deF| """)
    val lexer4 = new Lexer(reader4)
    assert(lexer4.nextToken === SymbolLit("abc deF"))

    val reader5 = new StringReader(""" 
|abc
deF| 
""")
    val lexer5 = new Lexer(reader5)
    assert(lexer5.nextToken === SymbolLit(
"""abc
deF"""))


    assert(lexUniqueToken(""" AbCdEf """) === SymbolLit("AbCdEf"))
    assert(lexUniqueToken(""" abc!def """) === SymbolLit("abc!def"))
    assert(lexUniqueToken(""" a@$%f """) === SymbolLit("a@$%f"))
    assert(lexUniqueToken(""" _+_ """) === SymbolLit("_+_"))
    assert(lexUniqueToken(""" <= """) === SymbolLit("<="))
    assert(lexUniqueToken(""" /// """) === SymbolLit("///"))
    assert(lexUniqueToken("""<abc>""") === SymbolLit("<abc>"))
    assert(lexUniqueToken(""".42""") === SymbolLit(".42"))

    assert(lexUniqueToken("""||""") === SymbolLit(""))
    assert(lexUniqueToken("""|af klj^*(0(&*)&(#^>>?"']]984|""") === SymbolLit("""af klj^*(0(&*)&(#^>>?"']]984"""))
  }

  test("keywords") {
    val reader1 = new StringReader(""" :d12 """)
    val lexer1 = new Lexer(reader1)
    assert(lexer1.nextToken === Keyword("d12"))

    val reader2 = new StringReader(""" :def """)
    val lexer2 = new Lexer(reader2)
    assert(lexer2.nextToken === Keyword("def"))

    val reader4 = new StringReader(""" |abc : deF| """)
    val lexer4 = new Lexer(reader4)
    assert(lexer4.nextToken === SymbolLit("abc : deF"))

    val reader5 = new StringReader(""" :|deF| """)
    val lexer5 = new Lexer(reader5)
    assert(lexer5.nextToken === Keyword("deF"))

    assert(lexUniqueToken(""":42""") === Keyword("42"))
    assert(lexUniqueToken(""":->""") === Keyword("->"))
    assert(lexUniqueToken(""":~=""") === Keyword("~="))
  }

  test("lexer compose") {
    val reader1 = new StringReader("""
      (test "test")
    """)
    val lexer1 = new Lexer(reader1)
    assert(lexer1.nextToken === OParen())
    assert(lexer1.nextToken === SymbolLit("test"))
    assert(lexer1.nextToken === StringLit("test"))
    assert(lexer1.nextToken === CParen())


    val reader2 = new StringReader("""
      ) (  42  42.173
    """)
    val lexer2 = new Lexer(reader2)
    assert(lexer2.nextToken === CParen())
    assert(lexer2.nextToken === OParen())
    assert(lexer2.nextToken === NumeralLit(42))
    assert(lexer2.nextToken === DecimalLit(42.173))

    val reader3 = new StringReader("""
      ) ;(  42  42.173
      12 "salut" ; """)
    val lexer3 = new Lexer(reader3)
    assert(lexer3.nextToken === CParen())
    assert(lexer3.nextToken === NumeralLit(12))
    assert(lexer3.nextToken === StringLit("salut"))
  }

  test("interactive lexer") {
    val pis = new SynchronousPipedReader
    /*
     * Since the pipe is empty, the lexer should not even start to read
     * in the reader. It should only start reading when asked for the nextToken token.
     */
    val lexer = failAfter(3 seconds) { new Lexer(pis) }
    /* 
     * this is impossible for the lexer to determine whether the token is terminated 
     * or if the nextToken char takes time to arrive, so we need some syntactic separation
     * hence the space after 12
     */
    pis.write("12 ")
    assert(lexer.nextToken === NumeralLit(12))
    pis.write("(")
    assert(lexer.nextToken === OParen())
    pis.write(")")
    assert(lexer.nextToken === CParen())
    pis.write("\"abcd\"")
    assert(lexer.nextToken === StringLit("abcd"))
  }

  test("Positions of tokens") {
    val reader1 = new StringReader("12")
    val lexer1 = new Lexer(reader1)
    val token1 = lexer1.nextToken
    assert(token1 === NumeralLit(12))
    assert(token1.getPos == Position(1, 1))

    val reader2 = new StringReader("  12 ")
    val lexer2 = new Lexer(reader2)
    val token2 = lexer2.nextToken
    assert(token2 === NumeralLit(12))
    assert(token2.getPos == Position(1, 3))

    val reader3 = new StringReader("""(test "test")""")
    val lexer3 = new Lexer(reader3)
    val token31 = lexer3.nextToken
    val token32 = lexer3.nextToken
    val token33 = lexer3.nextToken
    val token34 = lexer3.nextToken
    assert(token31 === OParen())
    assert(token31.getPos === Position(1,1))
    assert(token32 === SymbolLit("test"))
    assert(token32.getPos === Position(1,2))
    assert(token33 === StringLit("test"))
    assert(token33.getPos === Position(1,7))
    assert(token34 === CParen())
    assert(token34.getPos === Position(1,13))

    val reader4 = new StringReader(
"""test
  12
 )""")
    val lexer4 = new Lexer(reader4)
    val token41 = lexer4.nextToken
    val token42 = lexer4.nextToken
    val token43 = lexer4.nextToken
    assert(token41 === SymbolLit("test"))
    assert(token41.getPos === Position(1,1))
    assert(token42 === NumeralLit(12))
    assert(token42.getPos === Position(2,3))
    assert(token43 === CParen())
    assert(token43.getPos === Position(3,2))
  }

  test("Positions of parenthesis") {
    val reader = new StringReader("()()()")
    val lexer = new Lexer(reader)
    val token1 = lexer.nextToken
    val token2 = lexer.nextToken
    val token3 = lexer.nextToken
    val token4 = lexer.nextToken
    val token5 = lexer.nextToken
    val token6 = lexer.nextToken
    assert(token1 === OParen())
    assert(token1.getPos == Position(1, 1))
    assert(token2 === CParen())
    assert(token2.getPos == Position(1, 2))
    assert(token3 === OParen())
    assert(token3.getPos == Position(1, 3))
    assert(token4 === CParen())
    assert(token4.getPos == Position(1, 4))
    assert(token5 === OParen())
    assert(token5.getPos == Position(1, 5))
    assert(token6 === CParen())
    assert(token6.getPos == Position(1, 6))
  }

  test("Reserved words") {
    assert(lexUniqueToken("par") === Par())
    assert(lexUniqueToken("NUMERAL") === NUMERAL())
    assert(lexUniqueToken("DECIMAL") === DECIMAL())
    assert(lexUniqueToken("STRING") === STRING())
    assert(lexUniqueToken("_") === Underscore())
    assert(lexUniqueToken("!") === ExclamationMark())
    assert(lexUniqueToken("as") === As())
    assert(lexUniqueToken("let") === Let())
    assert(lexUniqueToken("forall") === ForAll())
    assert(lexUniqueToken("exists") === Exists())

    assert(lexUniqueToken("assert") === Assert())
    assert(lexUniqueToken("check-sat") === CheckSat())
    assert(lexUniqueToken("declare-sort") === DeclareSort())
    assert(lexUniqueToken("declare-fun") === DeclareFun())
    assert(lexUniqueToken("define-sort") === DefineSort())
    assert(lexUniqueToken("define-fun") === DefineFun())
    assert(lexUniqueToken("exit") === Exit())
    assert(lexUniqueToken("get-assertions") === GetAssertions())
    assert(lexUniqueToken("get-assignment") === GetAssignment())
    assert(lexUniqueToken("get-info") === GetInfo())
    assert(lexUniqueToken("get-option") === GetOption())
    assert(lexUniqueToken("get-proof") === GetProof())
    assert(lexUniqueToken("get-unsat-core") === GetUnsatCore())
    assert(lexUniqueToken("get-value") === GetValue())
    assert(lexUniqueToken("pop") === Pop())
    assert(lexUniqueToken("push") === Push())
    assert(lexUniqueToken("set-logic") === SetLogic())
    assert(lexUniqueToken("set-info") === SetInfo())
    assert(lexUniqueToken("set-option") === SetOption())
    assert(lexUniqueToken("declare-datatypes") === DeclareDatatypes())
  }

  test("Parentheses ending token") {
    val reader1 = new StringReader("12)")
    val lexer1 = new Lexer(reader1)
    assert(lexer1.nextToken === NumeralLit(12))
    assert(lexer1.nextToken === CParen())

    val reader2 = new StringReader("abc)")
    val lexer2 = new Lexer(reader2)
    assert(lexer2.nextToken === SymbolLit("abc"))
    assert(lexer2.nextToken === CParen())
  }

  test("Unexpected EOF") {
    val reader1 = new StringReader(""" "abcd """) //EOF while reading a string
    val lexer1 = new Lexer(reader1)
    val eofException1 = intercept[Lexer.UnexpectedEOFException] {
      lexer1.nextToken
    }
    assert(eofException1.position === Position(1, 7))

    val reader2 = new StringReader(""" "abcd \""") //EOF while reading a string
    val lexer2 = new Lexer(reader2)
    val eofException2 = intercept[Lexer.UnexpectedEOFException] {
      lexer2.nextToken
    }
    assert(eofException2.position === Position(1, 8))
  }

}
