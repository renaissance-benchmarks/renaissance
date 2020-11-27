package smtlib
package printer

import trees.Commands._
import trees.CommandsResponses._
import trees.Terms._
import trees.Tree

import java.io.Writer

object RecursivePrinter extends Printer {

  override val name: String = "recursive-printer"

  override protected def newContext(writer: Writer): PrintingContext = new PrintingContext(writer)
}
