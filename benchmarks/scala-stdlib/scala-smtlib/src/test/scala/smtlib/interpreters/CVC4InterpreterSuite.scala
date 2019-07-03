package smtlib
package interpreters

import org.scalatest.FunSuite

class CVC4InterpreterSuite extends FunSuite {

  private def getInterpreter: Option[CVC4Interpreter] = try {
    Some(new CVC4Interpreter)
  } catch {
    case (e: Exception) => None
  }


  //test("test resource") {

  //  getInterpreter.foreach(interpreter => {
  //    val smtFile = new java.io.InputStreamReader(getClass.getResourceAsStream("/test.smt2"))

  //    val lexer = new smtlib.lexer.Lexer(smtFile)
  //    val parser = new smtlib.parser.Parser(lexer)

  //    while(true) {
  //      val cmd = parser.parseCommand
  //      println("cmd: " + cmd)
  //      println("res: " + interpreter.eval(cmd))
  //    }
  //  })

  //}



}
