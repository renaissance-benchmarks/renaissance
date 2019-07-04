package smtlib
package interpreters

import lexer.Lexer
import parser.Parser
import parser.Commands._
import parser.CommandsResponses._
import printer.PrettyPrinter

//import scala.sys.process._
import java.io._

class Z3Interpreter extends ProcessInterpreter {


  protected override val process = new ProcessBuilder("z3", "-in", "-smt2").redirectErrorStream(true).start

  PrettyPrinter.printCommand(SetOption(PrintSuccess(true)), in)
  in.write("\n")
  in.flush
  parser.parseGenResponse

}
