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
// Work around @Repeatable annotations not working in this Scala version.
@Parameters(
  Array(
    new Parameter(name = "input_path", defaultValue = "/shakespeare.txt"),
    new Parameter(name = "expected_hash", defaultValue = "7527985ec20d9aab")
  )
)
@Configurations(
  Array(
    new Configuration(
      name = "test",
      settings =
        Array("input_path = /shakespeare-truncated.txt", "expected_hash = a7b6836b27dbdf0f")
    ),
    new Configuration(name = "jmh")
  )
)
final class RxScrabble extends Benchmark {

  // TODO: Consolidate benchmark parameters across the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/27

  private var inputPathParam: String = _

  private var expectedHashParam: String = _

  private val scrabblePath: String = "/scrabble.txt"

  private var bench: RxScrabbleImplementation = _

  override def setUpBeforeAll(c: BenchmarkContext): Unit = {
    inputPathParam = c.stringParameter("input_path")
    expectedHashParam = c.stringParameter("expected_hash")
    bench = new RxScrabbleImplementation(scrabblePath, inputPathParam)
  }

  override def runIteration(c: BenchmarkContext): BenchmarkResult = {
    val result = bench.runScrabble()

    new BenchmarkResult {
      override def validate() = {
        val actualWords = RxScrabbleImplementation.prepareForValidation(result)
        val hasher = new HashingResult(expectedHashParam, actualWords)
        hasher.validate()
      }
    }
  }
}
