package org.renaissance.jdk.streams

import org.renaissance.{Config, License, RenaissanceBenchmark}

class Mnemonics extends RenaissanceBenchmark {
  def description = "Solves the phone mnemonics problem using JDK streams."

  override def defaultRepetitions = 16

  def licenses = License.create(License.MIT)

  var testInput: String = null

  var coder: MnemonicsCoderWithStream = null

  override def setUpBeforeAll(c: Config): Unit = {
    testInput = "72252762577225276257528249849874238824"
    coder = new MnemonicsCoderWithStream(
      java.util.Arrays.asList(
        "Scala",
        "rocks",
        "Pack",
        "brocks",
        "GWT",
        "implicit",
        "nice",
        "ScalaGWT",
        "cat",
        "EFPL",
        "Lausanne",
        "sCala",
        "ROcks",
        "pAck",
        "Java",
        "Apple",
        "Google",
        "Rochester",
        "Utah",
        "Rice",
        "wyr",
        "lxm",
        "q",
        "w",
        "e",
        "r",
        "t",
        "y",
        "u",
        "i",
        "o",
        "p",
        "a",
        "s",
        "d",
        "f"
      )
    )
  }

  override def runIteration(c: Config): Unit = {
    blackHole(coder.translate(testInput))
  }
}
