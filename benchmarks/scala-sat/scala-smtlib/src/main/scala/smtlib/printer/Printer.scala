package smtlib
package printer

import trees.Commands._
import trees.CommandsResponses._
import trees.Terms._
import trees.Tree

import java.io.Writer
import java.io.StringWriter
import java.io.BufferedWriter

trait Printer {

  val name: String

  protected def newContext(writer: Writer): PrintingContext

  private def print(tree: Tree, writer: Writer): Unit = newContext(writer).output(tree)

  def printTerm(term: Term, writer: Writer): Unit = print(term, writer)
  def printSort(sort: Sort, writer: Writer): Unit = print(sort, writer)
  def printCommand(cmd: Command, writer: Writer): Unit = print(cmd, writer)
  def printCommandResponse(resp: CommandResponse, writer: Writer): Unit = print(resp, writer)
  def printSExpr(sexpr: SExpr, writer: Writer): Unit = print(sexpr, writer)

  def printScript(script: Script, writer: Writer): Unit = {
    for (cmd <- script.commands) printCommand(cmd, writer)
  }

  private def treeToString(tree: Tree): String = {
    val output = new StringWriter
    val writer = new BufferedWriter(output)
    print(tree, writer)
    writer.flush()
    output.toString
  }

  def toString(term: Term): String = treeToString(term)
  def toString(sort: Sort): String = treeToString(sort)
  def toString(command: Command): String = treeToString(command)
  def toString(response: CommandResponse): String = treeToString(response)
  def toString(sexpr: SExpr): String = treeToString(sexpr)

  def toString(script: Script): String = {
    val output = new StringWriter
    val writer = new BufferedWriter(output)
    for (cmd <- script.commands) printCommand(cmd, writer)
    writer.flush()
    output.toString
  }

}
