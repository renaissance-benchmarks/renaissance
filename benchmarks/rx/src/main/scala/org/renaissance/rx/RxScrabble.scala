package org.renaissance.rx

import org.renaissance.Benchmark
import org.renaissance.Benchmark._
import org.renaissance.BenchmarkContext
import org.renaissance.BenchmarkResult
import org.renaissance.BenchmarkResult.Validators
import org.renaissance.License

@Name("rx-scrabble")
@Group("rx")
@Summary("Solves the Scrabble puzzle using the Rx streams.")
@Licenses(Array(License.GPL2))
@Repetitions(80)
@Parameter(name = "input_path", defaultValue = "/shakespeare.txt")
@Parameter(name = "expected_hash", defaultValue = "7527985ec20d9aab")
@Configuration(
  name = "test",
  settings =
    Array("input_path = /shakespeare-truncated.txt", "expected_hash = a7b6836b27dbdf0f")
)
@Configuration(name = "jmh")
final class RxScrabble extends Benchmark {

  // TODO: Consolidate benchmark parameters across the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/27

  private var expectedHashParam: String = _

  private val scrabblePath: String = "/scrabble.txt"

  private var bench: RxScrabbleImplementation = _

  override def setUpBeforeAll(c: BenchmarkContext): Unit = {
    val inputPathParam = c.parameter("input_path").value
    expectedHashParam = c.parameter("expected_hash").value
    bench = new RxScrabbleImplementation(scrabblePath, inputPathParam)
  }

  override def run(c: BenchmarkContext): BenchmarkResult = {
    val result = bench.runScrabble()

    new BenchmarkResult {
      override def validate(): Unit = {
        val actualWords = RxScrabbleImplementation.prepareForValidation(result)
        Validators.hashing(expectedHashParam, actualWords).validate()
      }
    }
  }
}
