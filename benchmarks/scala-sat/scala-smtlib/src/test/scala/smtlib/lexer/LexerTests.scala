package smtlib
package lexer

import Tokens._
import common._
import Lexer.UnexpectedCharException
import Lexer.IllegalTokenException

import java.io.StringReader

import org.scalatest.concurrent.TimeLimits
import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.time.SpanSugar._


class LexerTests extends AnyFunSuite with TimeLimits {


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

  test("semicolon as part of string literal does not start a comment") {
    assert(lexUniqueToken(""" "Hey ;there" """) === StringLit("Hey ;there"))
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

  test("numeral cannot have leading 0") {
    intercept[IllegalTokenException] {
      lexUniqueToken("012")
    }
    intercept[IllegalTokenException] {
      lexUniqueToken("0041")
    }
  }

  test("decimal cannot have leading 0") {
    intercept[IllegalTokenException] {
      lexUniqueToken("012.12")
    }
    intercept[IllegalTokenException] {
      lexUniqueToken("0041.11")
    }
  }

  test("decimal can have leading 0 after the decimal point") {
    assert(lexUniqueToken("12.012") === DecimalLit(12.012))
    assert(lexUniqueToken("12.0012") === DecimalLit(12.0012))
  }

  test("hexadecimal can be a mix of lower and upper case") {
    assert(lexUniqueToken("#x0aBcD") === HexadecimalLit(Hexadecimal.fromString("0abcd").get))
    assert(lexUniqueToken("#x0ABCD") === HexadecimalLit(Hexadecimal.fromString("0abcd").get))
    assert(lexUniqueToken("#x0abcd") === HexadecimalLit(Hexadecimal.fromString("0ABCD").get))
  }

  test("string literals") {
    val reader1 = new StringReader(""" "12" """)
    val lexer1 = new Lexer(reader1)
    assert(lexer1.nextToken === StringLit("12"))

    assert(lexUniqueToken(""" "abcdefg" """) === StringLit("abcdefg"))
  }

  test("String literal can contain spaces") {
    assert(lexUniqueToken(""" "abc def" """) === StringLit("abc def"))
    assert(lexUniqueToken(""" " abc def " """) === StringLit(" abc def "))
  }

  test("Two consecutive quotes in string literal becomes a quote") {
    assert(lexUniqueToken(""" "abc""d""efg" """) === StringLit("""abc"d"efg"""))
    assert(lexUniqueToken(""" "She said: ""bye bye"" and left." """) ===
           StringLit("""She said: "bye bye" and left."""))
  }

  test("Backslash in string literal is raw") {
    assert(lexUniqueToken(""" "abc\ndef" """) === StringLit("""abc\ndef"""))
    assert(lexUniqueToken(""" "abc\n def" """) === StringLit("""abc\n def"""))
    assert(lexUniqueToken(""" "123\d456" """) === StringLit("""123\d456"""))

    assert(lexUniqueToken(""" "123\\456" """) === StringLit("""123\\456"""))
    assert(lexUniqueToken(""" "test\\" """) === StringLit("""test\\"""))
  }

  test("Backslash in string does not escape a quote") {
    val reader2 = new StringReader(""" "abc\" """)
    val lexer2 = new Lexer(reader2)
    assert(lexer2.nextToken === StringLit("""abc\"""))

    val reader3 = new StringReader(""" " abc \" " def" """)
    val lexer3 = new Lexer(reader3)
    assert(lexer3.nextToken === StringLit(""" abc \"""))
    assert(lexer3.nextToken === StringLit(""" def"""))

    val reader4 = new StringReader(""" "\"abc"\" """)
    val lexer4 = new Lexer(reader4)
    assert(lexer4.nextToken === StringLit("""\"""))
    assert(lexer4.nextToken === SymbolLit("abc"))
    assert(lexer4.nextToken === StringLit("""\"""))

  }


  test("lower case alphabetical symbols are correctly lexed") {
    assert(lexUniqueToken("abcd") === SymbolLit("abcd"))
    assert(lexUniqueToken("aaa") === SymbolLit("aaa"))
  }

  test("symbols can contain upper case and are case sensitive") {
    assert(lexUniqueToken("ABCD") === SymbolLit("ABCD"))
    assert(lexUniqueToken("XYZ") === SymbolLit("XYZ"))
    assert(lexUniqueToken(""" AbCdEf """) === SymbolLit("AbCdEf"))
  }

  test("Symbols can be single letter") {
    assert(lexUniqueToken("h") === SymbolLit("h"))
  }

  test("Symbols can contain digits") {
    assert(lexUniqueToken("d12") === SymbolLit("d12"))
    assert(lexUniqueToken("ab42cd") === SymbolLit("ab42cd"))
    assert(lexUniqueToken("a1b2c3") === SymbolLit("a1b2c3"))
  }

  test("symbols cannot contain backslashes") {
    intercept[UnexpectedCharException] {
      val reader = new StringReader("""abc\def""")
      val lexer = new Lexer(reader)
      assert(lexer.nextToken === SymbolLit("abc"))
      lexer.nextToken
    }
    intercept[UnexpectedCharException] {
      val reader = new StringReader("""abc\ def""")
      val lexer = new Lexer(reader)
      assert(lexer.nextToken === SymbolLit("abc"))
      lexer.nextToken
    }
    intercept[UnexpectedCharException] {
      val reader = new StringReader("""x\ng""")
      val lexer = new Lexer(reader)
      assert(lexer.nextToken === SymbolLit("x"))
      lexer.nextToken
    }
  }
  test("quoted symbols cannot contain backslashes") {
    intercept[UnexpectedCharException] {
      lexUniqueToken("""|abc\def|""")
    }
  }

  test("quoted symbols can have spaces") {
    assert(lexUniqueToken("|abc deF|") === SymbolLit("abc deF"))
  }

  test("quoted symbols can have new lines") {
    assert(lexUniqueToken("""|abc
deF| 
""") === SymbolLit("""abc
deF"""))
    assert(lexUniqueToken(
"""|hey there,
What's up?

See you!|""") === SymbolLit(
"""hey there,
What's up?

See you!"""))
  }

  test("symbols can contain special characters") {
    assert(lexUniqueToken(""" abc!def """) === SymbolLit("abc!def"))
    assert(lexUniqueToken(""" a@$%f """) === SymbolLit("a@$%f"))
    assert(lexUniqueToken(""" _+_ """) === SymbolLit("_+_"))
    assert(lexUniqueToken(""" <= """) === SymbolLit("<="))
    assert(lexUniqueToken(""" /// """) === SymbolLit("///"))
    assert(lexUniqueToken("""<abc>""") === SymbolLit("<abc>"))
    assert(lexUniqueToken(""".42""") === SymbolLit(".42"))
    assert(lexUniqueToken("""*$s&6""") === SymbolLit("*$s&6"))
    assert(lexUniqueToken("""abc.def""") === SymbolLit("abc.def"))
  }

  test("Digits with leading +/- are actually symbols") {
    assert(lexUniqueToken("""+34""") === SymbolLit("+34"))
    assert(lexUniqueToken("""-7""") === SymbolLit("-7"))
  }

  test("Symbols can start with underscore") {
    assert(lexUniqueToken("""_ufmt_1""") === SymbolLit("_ufmt_1"))
  }

  test("symbols cannot start with a digit") {
    val reader = new StringReader("""12x_ng""")
    val lexer = new Lexer(reader)
    assert(lexer.nextToken === NumeralLit(12))
  }

  test("symbols can have a really weird name") {
    assert(lexUniqueToken("""||""") === SymbolLit(""))
    assert(lexUniqueToken("""|af klj^*(0(&*)&(#^>>?"']]984|""") === SymbolLit("""af klj^*(0(&*)&(#^>>?"']]984"""))
  }

  test("quoted simple symbols can be equals to simple symbols") {
    assert(lexUniqueToken("|abc|") === lexUniqueToken("abc"))
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
    assert(lexer1.nextToken.kind === OParen)
    assert(lexer1.nextToken === SymbolLit("test"))
    assert(lexer1.nextToken === StringLit("test"))
    assert(lexer1.nextToken.kind === CParen)


    val reader2 = new StringReader("""
      ) (  42  42.173
    """)
    val lexer2 = new Lexer(reader2)
    assert(lexer2.nextToken.kind === CParen)
    assert(lexer2.nextToken.kind === OParen)
    assert(lexer2.nextToken === NumeralLit(42))
    assert(lexer2.nextToken === DecimalLit(42.173))

    val reader3 = new StringReader("""
      ) ;(  42  42.173
      12 "salut" ; """)
    val lexer3 = new Lexer(reader3)
    assert(lexer3.nextToken.kind === CParen)
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
    assert(lexer.nextToken.kind === OParen)
    pis.write(")")
    assert(lexer.nextToken.kind === CParen)
    pis.write("\"abcd\" ")
    assert(lexer.nextToken === StringLit("abcd"))
  }

  test("Tokens have proper positions") {
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
    assert(token31.kind === OParen)
    assert(token31.getPos === Position(1,1))
    assert(token32 === SymbolLit("test"))
    assert(token32.getPos === Position(1,2))
    assert(token33 === StringLit("test"))
    assert(token33.getPos === Position(1,7))
    assert(token34.kind === CParen)
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
    assert(token43.kind === CParen)
    assert(token43.getPos === Position(3,2))
  }

  test("Parenthesis have proper positions") {
    val reader = new StringReader("()()()")
    val lexer = new Lexer(reader)
    val token1 = lexer.nextToken
    val token2 = lexer.nextToken
    val token3 = lexer.nextToken
    val token4 = lexer.nextToken
    val token5 = lexer.nextToken
    val token6 = lexer.nextToken
    assert(token1.kind === OParen)
    assert(token1.getPos == Position(1, 1))
    assert(token2.kind === CParen)
    assert(token2.getPos == Position(1, 2))
    assert(token3.kind === OParen)
    assert(token3.getPos == Position(1, 3))
    assert(token4.kind === CParen)
    assert(token4.getPos == Position(1, 4))
    assert(token5.kind === OParen)
    assert(token5.getPos == Position(1, 5))
    assert(token6.kind === CParen)
    assert(token6.getPos == Position(1, 6))
  }

  test("Reserved keywords are properly lexed") {
    assert(lexUniqueToken("BINARY").kind === BINARY)
    assert(lexUniqueToken("DECIMAL").kind === DECIMAL)
    assert(lexUniqueToken("HEXADECIMAL").kind === HEXADECIMAL)
    assert(lexUniqueToken("NUMERAL").kind === NUMERAL)
    assert(lexUniqueToken("STRING").kind === STRING)
    assert(lexUniqueToken("_").kind === Underscore)
    assert(lexUniqueToken("!").kind === ExclamationMark)
    assert(lexUniqueToken("as").kind === As)
    assert(lexUniqueToken("let").kind === Let)
    assert(lexUniqueToken("forall").kind === Forall)
    assert(lexUniqueToken("exists").kind === Exists)
    assert(lexUniqueToken("par").kind === Par)

    assert(lexUniqueToken("assert").kind === Assert)
    assert(lexUniqueToken("check-sat").kind === CheckSat)
    assert(lexUniqueToken("check-sat-assuming").kind === CheckSatAssuming)
    assert(lexUniqueToken("declare-const").kind === DeclareConst)
    assert(lexUniqueToken("declare-fun").kind === DeclareFun)
    assert(lexUniqueToken("declare-sort").kind === DeclareSort)
    assert(lexUniqueToken("define-fun").kind === DefineFun)
    assert(lexUniqueToken("define-fun-rec").kind === DefineFunRec)
    assert(lexUniqueToken("define-funs-rec").kind === DefineFunsRec)
    assert(lexUniqueToken("define-sort").kind === DefineSort)
    assert(lexUniqueToken("echo").kind === Echo)
    assert(lexUniqueToken("exit").kind === Exit)
    assert(lexUniqueToken("get-assertions").kind === GetAssertions)
    assert(lexUniqueToken("get-assignment").kind === GetAssignment)
    assert(lexUniqueToken("get-info").kind === GetInfo)
    assert(lexUniqueToken("get-model").kind === GetModel)
    assert(lexUniqueToken("get-option").kind === GetOption)
    assert(lexUniqueToken("get-proof").kind === GetProof)
    assert(lexUniqueToken("get-unsat-assumptions").kind === GetUnsatAssumptions)
    assert(lexUniqueToken("get-unsat-core").kind === GetUnsatCore)
    assert(lexUniqueToken("get-value").kind === GetValue)
    assert(lexUniqueToken("pop").kind === Pop)
    assert(lexUniqueToken("push").kind === Push)
    assert(lexUniqueToken("reset").kind === Reset)
    assert(lexUniqueToken("reset-assertions").kind === ResetAssertions)
    assert(lexUniqueToken("set-logic").kind === SetLogic)
    assert(lexUniqueToken("set-info").kind === SetInfo)
    assert(lexUniqueToken("set-logic").kind === SetLogic)
    assert(lexUniqueToken("set-option").kind === SetOption)


    assert(lexUniqueToken("declare-datatypes").kind === DeclareDatatypes)
  }

  test("Parentheses ending token") {
    val reader1 = new StringReader("12)")
    val lexer1 = new Lexer(reader1)
    assert(lexer1.nextToken === NumeralLit(12))
    assert(lexer1.nextToken.kind === CParen)

    val reader2 = new StringReader("abc)")
    val lexer2 = new Lexer(reader2)
    assert(lexer2.nextToken === SymbolLit("abc"))
    assert(lexer2.nextToken.kind === CParen)
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
