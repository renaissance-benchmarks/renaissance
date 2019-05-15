package org.renaissance.jdk.streams

import org.renaissance.Config
import org.renaissance.License
import org.renaissance.RenaissanceBenchmark
import org.renaissance.Benchmark._

@Name("par-mnemonics")
@Group("jdk-streams")
@Summary("Solves the phone mnemonics problem using parallel JDK streams.")
@Licenses(Array(License.MIT))
@Repetitions(16)
class ParMnemonics extends RenaissanceBenchmark {

  var testInput: String = null

  var coder: MnemonicsCoderWithStream = null

  override def setUpBeforeAll(c: Config): Unit = {
    testInput = "72252762577225276257528249849874238824"
    if (c.functionalTest) {
      testInput = "7225276257722527"
    }
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
    blackHole(coder.parallelTranslate(testInput))
  }
}
