package smtlib

import parser.Commands.{Script, Command}
import parser.CommandsResponses.CommandResponse
import parser.Parser

/*
 * An interpreter is a stateful object that can eval Commands and returns
 * CommandResponse.
 *
 * Note that despite returning the command response, the interpreter should handle the printing
 * of those responses itself. That is because it needs to handle the verbosity and *-output-channel
 * options commands, and will do the correct printing depending on the internal state.
 * The responses are returned as a way to progamatically communicate with a solver.

 * TODO: The interaction of the set-option for the channels with the eval interface
         seems just wrong. Need to clarify that.
 */
trait Interpreter {

  def eval(cmd: Command): CommandResponse

  //A free method is kind of justified by the need for the IO streams to be closed, and
  //there seems to be a decent case in general to have such a method for things like solvers
  //note that free can be used even if the solver is currently solving, and act as a sort of interrupt
  def free(): Unit

}

object Interpreter {

  import java.io.Reader
  import java.io.FileReader
  import java.io.BufferedReader
  import java.io.File

  def execute(script: Script)(implicit interpreter: Interpreter): Unit = {
    for(cmd <- script.commands)
      interpreter.eval(cmd)
  }

  def execute(scriptReader: Reader)(implicit interpreter: Interpreter): Unit = {
    val parser = new Parser(new lexer.Lexer(scriptReader))
    var cmd: Command = null
    do {
      val cmd = parser.parseCommand
      if(cmd != null)
        interpreter.eval(cmd)
    } while(cmd != null)
  }

  def execute(file: File)(implicit interpreter: Interpreter): Unit = {
    val parser = new Parser(new lexer.Lexer(new BufferedReader(new FileReader(file))))
    var cmd: Command = null
    do {
      cmd = parser.parseCommand
      if(cmd != null)
        interpreter.eval(cmd)
    } while(cmd != null)
  }

}
