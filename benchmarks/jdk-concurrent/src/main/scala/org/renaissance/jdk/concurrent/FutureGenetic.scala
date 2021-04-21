package org.renaissance.jdk.concurrent

import org.renaissance.Benchmark
import org.renaissance.Benchmark._
import org.renaissance.BenchmarkContext
import org.renaissance.BenchmarkResult
import org.renaissance.BenchmarkResult.Validators
import org.renaissance.License

@Name("future-genetic")
@Group("jdk-concurrent")
@Summary("Runs a genetic algorithm using the Jenetics library and futures.")
@Licenses(Array(License.APACHE2))
@Repetitions(50)
@Parameter(name = "chromosome_count", defaultValue = "50")
@Parameter(name = "generation_count", defaultValue = "5000")
@Configuration(
  name = "test",
  settings = Array("chromosome_count = 10", "generation_count = 200")
)
@Configuration(name = "jmh")
final class FutureGenetic extends Benchmark {

  // TODO: Consolidate benchmark parameters across the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/27

  private var chromosomeCountParam: Int = _

  private var generationCountParam: Int = _

  private val THREAD_COUNT = 2

  private val RANDOM_SEED = 7

  private val GENE_MIN_VALUE = -2000

  private val GENE_MAX_VALUE = 2000

  private val GENE_COUNT = 200

  private var benchmark: JavaJenetics = _

  override def setUpBeforeAll(c: BenchmarkContext): Unit = {
    chromosomeCountParam = c.parameter("chromosome_count").toPositiveInteger
    generationCountParam = c.parameter("generation_count").toPositiveInteger

    benchmark = new JavaJenetics(
      GENE_MIN_VALUE,
      GENE_MAX_VALUE,
      GENE_COUNT,
      chromosomeCountParam,
      generationCountParam,
      THREAD_COUNT,
      RANDOM_SEED
    )

    benchmark.setupBeforeAll()
  }

  override def tearDownAfterAll(c: BenchmarkContext): Unit = {
    benchmark.tearDownAfterAll()
  }

  override def run(c: BenchmarkContext): BenchmarkResult = {
    val result = benchmark.runRepetition()

    // TODO: add proper validation
    Validators.dummy(result)
  }
}
