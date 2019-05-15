package org.renaissance.jdk.streams

import org.renaissance.Config
import org.renaissance.License
import org.renaissance.RenaissanceBenchmark
import org.renaissance.Benchmark._

@Name("scrabble")
@Group("jdk-streams")
@Summary("Solves the Scrabble puzzle using JDK Streams.")
@Licenses(Array(License.GPL2))
@Repetitions(50)
class Scrabble extends RenaissanceBenchmark {

  // TODO: Consolidate benchmark parameters across the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/27

  var shakespearePath = "/shakespeare.txt"

  var scrabblePath = "/scrabble.txt"

  var scrabble: JavaScrabble = null

  override def setUpBeforeAll(c: Config): Unit = {
    if (c.functionalTest) {
      shakespearePath = "/shakespeare-truncated.txt"
    }
    scrabble = new JavaScrabble(shakespearePath, scrabblePath)
  }

  override def runIteration(c: Config): Unit = {
    blackHole(scrabble.run())
  }
}
