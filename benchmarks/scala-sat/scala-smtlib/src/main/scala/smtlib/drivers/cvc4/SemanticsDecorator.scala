package smtlib
package drivers
package cvc4

import trees.Commands._


trait SemanticsDecorator extends SemanticsDriver {


  override def eval(cmd: Command): Unit = {
    super.eval(cmd)

    //TODO: add code specific to cvc4 to use the raw solver here
  }

}
