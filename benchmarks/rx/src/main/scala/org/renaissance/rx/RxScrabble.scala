package org.renaissance.rx

import org.renaissance.Config
import org.renaissance.License
import org.renaissance.RenaissanceBenchmark
import org.renaissance.Benchmark._

@Name("rx-scrabble")
@Group("rx")
@Summary("Solves the Scrabble puzzle using the Rx streams.")
@Licenses(Array(License.GPL2))
@Repetitions(80)
class RxScrabble extends RenaissanceBenchmark {

  // TODO: Consolidate benchmark parameters across the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/27

  var shakespearePath: String = "/shakespeare.txt"

  var scrabblePath: String = "/scrabble.txt"

  var bench: RxScrabbleImplementation = null

  override def setUpBeforeAll(c: Config): Unit = {
    if (c.functionalTest) {
      shakespearePath = "/shakespeare-truncated.txt"
    }
    bench = new RxScrabbleImplementation(scrabblePath, shakespearePath)
  }

  override def runIteration(c: Config): Unit = {
    blackHole(bench.runScrabble().size())
  }
}
