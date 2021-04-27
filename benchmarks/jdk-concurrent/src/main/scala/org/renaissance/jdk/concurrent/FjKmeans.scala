package org.renaissance.jdk.concurrent

import org.renaissance.Benchmark
import org.renaissance.Benchmark._
import org.renaissance.BenchmarkContext
import org.renaissance.BenchmarkResult
import org.renaissance.BenchmarkResult.Validators
import org.renaissance.License

@Name("fj-kmeans")
@Group("jdk-concurrent")
@Summary("Runs the k-means algorithm using the fork/join framework.")
@Licenses(Array(License.APACHE2))
@Repetitions(30)
@Parameter(name = "thread_count", defaultValue = "$cpu.count")
@Parameter(name = "vector_length", defaultValue = "500000")
@Configuration(name = "test", settings = Array("vector_length = 500"))
@Configuration(name = "jmh")
final class FjKmeans extends Benchmark {

  // TODO: Consolidate benchmark parameters across the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/27

  private var threadCountParam: Int = _

  private var vectorLengthParam: Int = _

  private val DIMENSION = 5

  private val CLUSTER_COUNT = 5

  private val ITERATION_COUNT = 50

  private val LOOP_COUNT = 4

  private var benchmark: JavaKMeans = _

  private var data: java.util.List[Array[java.lang.Double]] = _

  override def setUpBeforeAll(c: BenchmarkContext): Unit = {
    threadCountParam = c.parameter("thread_count").toInteger
    vectorLengthParam = c.parameter("vector_length").toInteger

    benchmark = new JavaKMeans(DIMENSION, threadCountParam)
    data = JavaKMeans.generateData(vectorLengthParam, DIMENSION, CLUSTER_COUNT)
  }

  override def run(c: BenchmarkContext): BenchmarkResult = {
    val results = for (_ <- 0 until LOOP_COUNT) yield {
      benchmark.run(CLUSTER_COUNT, data, ITERATION_COUNT)
    }

    // TODO: add proper validation of the individual sub-benchmarks
    Validators.dummy(results)
  }

  override def tearDownAfterAll(c: BenchmarkContext): Unit = {
    benchmark.tearDown()
    benchmark = null
    data = null
  }
}
