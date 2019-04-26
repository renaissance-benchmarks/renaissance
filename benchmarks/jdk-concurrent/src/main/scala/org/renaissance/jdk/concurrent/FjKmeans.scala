package org.renaissance.jdk.concurrent

import org.renaissance.Config
import org.renaissance.License
import org.renaissance.RenaissanceBenchmark

class FjKmeans extends RenaissanceBenchmark {
  def description = "Runs the k-means algorithm using the fork/join framework."

  override def defaultRepetitions = 30

  def licenses = License.create(License.APACHE2)

  private val DIMENSION = 5

  private val VECTOR_LENGTH = 500000

  private val CLUSTER_COUNT = 5

  private val ITERATION_COUNT = 50

  private val LOOP_COUNT = 4

  private val THREAD_COUNT = Runtime.getRuntime.availableProcessors

  private var benchmark: JavaKMeans = null

  private var data: java.util.List[Array[java.lang.Double]] = null

  override def setUpBeforeAll(c: Config): Unit = {
    benchmark = new JavaKMeans(DIMENSION, THREAD_COUNT)
    data = JavaKMeans.generateData(VECTOR_LENGTH, DIMENSION, CLUSTER_COUNT);
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
