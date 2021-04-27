package smtlib
package printer

import common.LinkedList

import trees.Commands._
import trees.CommandsResponses._
import trees.Terms._
import trees.Tree

import java.io.Writer

import scala.collection.mutable.Stack

object TailPrinter extends Printer {

  override val name: String = "tail-printer"

  override protected def newContext(writer: Writer) = new TailContext(writer)
}

class TailContext(writer: Writer) extends PrintingContext(writer) {
  var actions = new LinkedList[() => Unit]
  var actionStack = List[LinkedList[() => Unit]]()

  override def print(tree: Tree): Unit = {
    actions.append(() => super.print(tree))
  }

  override def print(str: String): Unit = {
    actions.append(() => super.print(str))
  }

  override protected def finish(): Unit = {
    while (!actions.isEmpty || !actionStack.isEmpty) {
      if (actions.isEmpty) {
        actions = actionStack.head
        actionStack = actionStack.tail
      } else {
        val action = actions.pop()
        actionStack ::= actions
        actions = new LinkedList[() => Unit]
        action()
      }
    }
  }
}
