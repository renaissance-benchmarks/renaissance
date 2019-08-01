package org.renaissance.jdk.concurrent

import org.renaissance.Benchmark
import org.renaissance.Benchmark._
import org.renaissance.BenchmarkContext
import org.renaissance.BenchmarkResult
import org.renaissance.License

@Name("fj-kmeans")
@Group("jdk-concurrent")
@Summary("Runs the k-means algorithm using the fork/join framework.")
@Licenses(Array(License.APACHE2))
@Repetitions(30)
@Parameter(name = "threads", defaultValue = "$cpu.count")
@Parameter(name = "dimension", defaultValue = "5")
@Parameter(name = "vector_length", defaultValue = "500000")
@Parameter(name = "cluster_count", defaultValue = "5")
@Parameter(name = "iteration_count", defaultValue = "50")
@Parameter(name = "loop_count", defaultValue = "4")
@Configuration(name = "default")
@Configuration(name = "test", settings = Array(
  "vector_length = 500"
))
class FjKmeans extends Benchmark {

  // TODO: Consolidate benchmark parameters across the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/27

  private val THREAD_COUNT = Runtime.getRuntime.availableProcessors

  private var DIMENSION = 5

  private var VECTOR_LENGTH = 500000

  private var CLUSTER_COUNT = 5

  private var ITERATION_COUNT = 50

  private var LOOP_COUNT = 4

  private var benchmark: JavaKMeans = null

  private var data: java.util.List[Array[java.lang.Double]] = null

  override def setUpBeforeAll(c: BenchmarkContext): Unit = {
    if (c.functionalTest) {
      DIMENSION = 5
      VECTOR_LENGTH = 500
      CLUSTER_COUNT = 5
      ITERATION_COUNT = 50
      LOOP_COUNT = 4
    }

    benchmark = new JavaKMeans(DIMENSION, THREAD_COUNT)
    data = JavaKMeans.generateData(VECTOR_LENGTH, DIMENSION, CLUSTER_COUNT)
  }

  override def runIteration(c: BenchmarkContext): BenchmarkResult = {
    for (i <- 0 until LOOP_COUNT) {
      c.blackHole(benchmark.run(CLUSTER_COUNT, data, ITERATION_COUNT))
    }

    // TODO: add proper validation of the individual sub-benchmarks
    BenchmarkResult.dummy()
  }

  override def tearDownAfterAll(c: BenchmarkContext): Unit = {
    benchmark.tearDown()
    benchmark = null
    data = null
  }
}
