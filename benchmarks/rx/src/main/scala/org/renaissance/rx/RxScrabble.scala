package org.renaissance.rx

import org.renaissance.Benchmark
import org.renaissance.Benchmark._
import org.renaissance.BenchmarkContext
import org.renaissance.BenchmarkResult
import org.renaissance.HashingResult
import org.renaissance.License

@Name("rx-scrabble")
@Group("rx")
@Summary("Solves the Scrabble puzzle using the Rx streams.")
@Licenses(Array(License.GPL2))
@Repetitions(80)
class RxScrabble extends Benchmark {

  // TODO: Consolidate benchmark parameters across the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/27

  var shakespearePath: String = "/shakespeare.txt"

  var scrabblePath: String = "/scrabble.txt"

  var bench: RxScrabbleImplementation = null

  override def setUpBeforeAll(c: BenchmarkContext): Unit = {
    if (c.functionalTest) {
      shakespearePath = "/shakespeare-truncated.txt"
    }

    bench = new RxScrabbleImplementation(scrabblePath, shakespearePath)
  }

  override def runIteration(c: BenchmarkContext): BenchmarkResult = {
    val result = bench.runScrabble()
    val expected = if (c.functionalTest) "a7b6836b27dbdf0f" else "7527985ec20d9aab"

    new BenchmarkResult {
      override def validate() = {
        val actualWords = RxScrabbleImplementation.prepareForValidation(result)
        val hasher = new HashingResult(expected, actualWords)
        hasher.validate()
      }
    }
  }
}
