package smtlib
package interpreters

import lexer.Lexer
import parser.Parser
import parser.Commands._
import parser.CommandsResponses._
import printer.PrettyPrinter

//import scala.sys.process._
import java.io._

class CVC4Interpreter extends Interpreter {

  private val cvc4 = new ProcessBuilder("cvc4",
                                                "-q",
                                                "--produce-models",
                                                "--no-incremental",
                                                "--tear-down-incremental",
                                                "--dt-rewrite-error-sel",
                                                "--print-success",
                                                "--lang", "smt").redirectErrorStream(true).start

  val cvc4In = new BufferedWriter(new OutputStreamWriter(cvc4.getOutputStream))
  val cvc4Out = new BufferedReader(new InputStreamReader(cvc4.getInputStream))

  val parser = new Parser(new Lexer(cvc4Out))

  override def eval(cmd: Command): CommandResponse = {
    PrettyPrinter.printCommand(cmd, cvc4In)
    cvc4In.write("\n")
    cvc4In.flush
    cmd match {
      case CheckSat() => parser.parseCheckSatResponse
      case GetAssertions() => parser.parseGetAssertionsResponse
      case GetUnsatCore() => parser.parseGetUnsatCoreResponse
      case GetProof() => parser.parseGetProofResponse
      case GetValue(_, _) => parser.parseGetValueResponse
      case GetAssignment() => parser.parseGetAssignmentResponse

      case GetOption(_) => parser.parseGetOptionResponse
      case GetInfo(_) => parser.parseGetInfoResponse

      case GetModel() => parser.parseGetModelResponse

      case _ => parser.parseGenResponse
    }
  }

  override def free(): Unit = {
    PrettyPrinter.printCommand(Exit(), cvc4In)
    cvc4In.write("\n")
    cvc4In.flush

    cvc4.destroy
    cvc4In.close
  }
}
