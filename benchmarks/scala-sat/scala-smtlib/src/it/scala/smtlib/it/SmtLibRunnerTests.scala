package smtlib
package it

import scala.sys.process._

import org.scalatest.funsuite.AnyFunSuite

import java.io.File
import java.io.FileReader

import parser.Parser
import lexer.Lexer
import printer.RecursivePrinter
import interpreters._


/** Checks the parser on .smt2 files.
  *
  * Compare the result of running command by command with an interpreter against
  * running the corresponding executable directly on the .smt2 files.
  *
  * TODO: proper way to display warning when not all tests are run because of not found executables.
  */
class SmtLibRunnerTests extends AnyFunSuite with TestHelpers {

  filesInResourceDir("regression/smtlib/solving/all", _.endsWith(".smt2")).foreach(file => {
    if(isZ3Available) {
      test("With Z3: SMTLIB benchmark: " + file.getPath) {
        compareWithInterpreter(executeZ3)(getZ3Interpreter, file)
      }
    }
    if(isCVC4Available) {
      test("With CVC4: SMTLIB benchmark: " + file.getPath) {
        compareWithInterpreter(executeCVC4)(getCVC4Interpreter, file)
      }
    }
  })

  if(isZ3Available) {
    filesInResourceDir("regression/smtlib/solving/z3", _.endsWith(".smt2")).foreach(file => {
      test("With Z3: SMTLIB benchmark: " + file.getPath) {
        compareWithInterpreter(executeZ3)(getZ3Interpreter, file)
      }
    })
  }

  if(isCVC4Available) {
    filesInResourceDir("regression/smtlib/solving/cvc4", _.endsWith(".smt2")).foreach(file => {
      test("With CVC4: SMTLIB benchmark: " + file.getPath) {
        compareWithWant(getCVC4Interpreter, file, new File(file.getPath + ".want"))
      }
    })
  }

  
  def compareWithInterpreter(executable: (File) => (String => Unit) => Unit)
                            (interpreter: Interpreter, file: File) = {
    val lexer = new Lexer(new FileReader(file))
    val parser = new Parser(lexer)

    executable(file) { (expected: String) =>
      val cmd = parser.parseCommand
      assert(cmd !== null)
      val res: String = interpreter.eval(cmd).toString
      assert(expected.trim === res.trim)
    }
    assert(parser.parseCommand === null)
  }

  def compareWithWant(interpreter: Interpreter, file: File, want: File) = {

    val lexer = new Lexer(new FileReader(file))
    val parser = new Parser(lexer)

    for(expected <- scala.io.Source.fromFile(want).getLines()) {
      val cmd = parser.parseCommand
      assert(cmd !== null)
      val res: String = interpreter.eval(cmd).toString
      assert(expected.trim === res.trim)
    }
    assert(parser.parseCommand === null)
    intercept[smtlib.parser.Parser.UnexpectedEOFException] {
      // There shouldn't be anything left on the interpreter parser (the solver process).
      interpreter.parser.parseSExpr
    }
  }
}
