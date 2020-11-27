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


class ProcessInterpreterTests extends AnyFunSuite with TestHelpers {

  //TODO: properly get all interpreters
  def interpreters: Seq[Interpreter] = Seq(getZ3Interpreter)

  test("Interrupt after free does not throw an exception") {
    //TODO: check against all interpreters
    val z3Interpreter = getZ3Interpreter

    z3Interpreter.eval(trees.Commands.SetLogic(trees.Commands.AUFLIA()))
    z3Interpreter.eval(trees.Commands.CheckSat())
    z3Interpreter.free()
    z3Interpreter.interrupt()
  }

  test("Interrupt can be called multiple times safely") {
    //TODO: check against all interpreters
    val z3Interpreter = getZ3Interpreter

    z3Interpreter.eval(trees.Commands.SetLogic(trees.Commands.AUFLIA()))
    z3Interpreter.eval(trees.Commands.CheckSat())
    z3Interpreter.interrupt()
    z3Interpreter.interrupt()
    z3Interpreter.interrupt()
    z3Interpreter.interrupt()
    z3Interpreter.interrupt()
  }


  //TODO: test interrupt on a long running check-sat command with big benchmarks

}
