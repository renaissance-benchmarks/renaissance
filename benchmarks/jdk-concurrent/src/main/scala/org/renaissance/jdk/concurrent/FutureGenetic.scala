package org.renaissance.jdk.concurrent

import io.jenetics.Chromosome
import io.jenetics.DoubleGene
import org.renaissance.Benchmark
import org.renaissance.Benchmark._
import org.renaissance.BenchmarkContext
import org.renaissance.BenchmarkResult
import org.renaissance.BenchmarkResult.Assert
import org.renaissance.License

import java.util.concurrent.ExecutorService
import java.util.concurrent.Executors
import java.util.concurrent.TimeUnit

@Name("future-genetic")
@Group("jdk-concurrent")
@Group("functional") // With Scala 3, the primary group goes last.
@Summary("Runs a genetic algorithm using the Jenetics library and futures.")
@Licenses(Array(License.APACHE2))
@Repetitions(50)
@Parameter(name = "population_size", defaultValue = "50")
@Parameter(name = "generation_count", defaultValue = "5000")
@Parameter(name = "expected_sum", defaultValue = "-10975.2462578835")
@Parameter(name = "expected_sum_squares", defaultValue = "130336964.45529507")
@Configuration(
  name = "test",
  settings = Array(
    "population_size = 10",
    "generation_count = 200",
    "expected_sum = -1857.224767254019",
    "expected_sum_squares = 135348190.4555571"
  )
)
@Configuration(name = "jmh")
final class FutureGenetic extends Benchmark {

  // TODO: Consolidate benchmark parameters across the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/27

  private var populationSizeParam: Int = _

  private var generationCountParam: Int = _

  private var expectedSum: Double = _

  private var expectedSumSquares: Double = _

  private val THREAD_COUNT = 2

  private val RANDOM_SEED = 7

  private val GENE_MIN_VALUE = -2000

  private val GENE_MAX_VALUE = 2000

  private val GENE_COUNT = 200

  //

  /** Executor to use for the GA tasks in each repetition. */
  private var executor: ExecutorService = _

  private var benchmark: JavaJenetics = _

  override def setUpBeforeAll(c: BenchmarkContext): Unit = {
    populationSizeParam = c.parameter("population_size").toPositiveInteger
    generationCountParam = c.parameter("generation_count").toPositiveInteger
    expectedSum = c.parameter("expected_sum").toDouble
    expectedSumSquares = c.parameter("expected_sum_squares").toDouble

    executor = Executors.newWorkStealingPool();

    benchmark = new JavaJenetics(
      GENE_MIN_VALUE,
      GENE_MAX_VALUE,
      GENE_COUNT,
      populationSizeParam,
      generationCountParam,
      THREAD_COUNT,
      RANDOM_SEED
    )
  }

  override def setUpBeforeEach(context: BenchmarkContext): Unit = {
    benchmark.setupBeforeEach()
  }

  private def validate(result: Chromosome[DoubleGene]): Unit = {
    def chromosomeGeneValues(result: Chromosome[DoubleGene]) = {
      result.stream().mapToDouble(_.allele().toDouble)
    }

    val EPSILON = 0.00001
    val actualSum = chromosomeGeneValues(result).sum()
    val actualSumSquares = chromosomeGeneValues(result).map(d => d * d).sum()

    Assert.assertEquals(expectedSum, actualSum, EPSILON, "sum of gene values")

    Assert.assertEquals(
      expectedSumSquares,
      actualSumSquares,
      EPSILON,
      "sum of squares of gene values"
    )
  }

  override def run(c: BenchmarkContext): BenchmarkResult = {
    val result = benchmark.runRepetition(executor)
    () => validate(result)
  }

  override def tearDownAfterAll(c: BenchmarkContext): Unit = {
    executor.shutdown()

    try {
      executor.awaitTermination(1, TimeUnit.SECONDS)
    } catch {
      case e: InterruptedException =>
        throw new RuntimeException(e)
    }
  }

}
