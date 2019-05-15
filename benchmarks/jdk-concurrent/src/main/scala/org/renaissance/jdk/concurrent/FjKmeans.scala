package org.renaissance.jdk.concurrent

import org.renaissance.Config
import org.renaissance.License
import org.renaissance.RenaissanceBenchmark
import org.renaissance.Benchmark._

@Name("fj-kmeans")
@Group("jdk-concurrent")
@Summary("Runs the k-means algorithm using the fork/join framework.")
@Licenses(Array(License.APACHE2))
@Repetitions(30)
class FjKmeans extends RenaissanceBenchmark {

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

  override def setUpBeforeAll(c: Config): Unit = {
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

  override def runIteration(c: Config): Unit = {
    for (i <- 0 until LOOP_COUNT) {
      blackHole(benchmark.run(CLUSTER_COUNT, data, ITERATION_COUNT))
    }
  }

  override def tearDownAfterAll(c: Config): Unit = {
    benchmark.tearDown()
    benchmark = null
    data = null
  }
}
