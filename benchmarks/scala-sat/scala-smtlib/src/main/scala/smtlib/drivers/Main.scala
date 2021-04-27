package smtlib
package drivers

import java.io.FileReader

import interpreters._
import lexer._
import parser._
import trees._

/** Provides an entry point to run a command line wrapper on a driver */
object Main {


  def main(args: Array[String]): Unit = {

    /*
     * first argument must be solver. Probably we should support notion of
     * version as well.
     */
    val solver = args(0)

    if(solver == "cvc4") {

      val cvc4Interpreter = CVC4Interpreter.buildDefault
      val l = new Lexer(new FileReader(args(1)))
      val p = new Parser(l)

      var cmd = p.parseCommand
      while(cmd != null) {
        println(cvc4Interpreter.eval(cmd))
        cmd = p.parseCommand
      }
    }

  }


}
