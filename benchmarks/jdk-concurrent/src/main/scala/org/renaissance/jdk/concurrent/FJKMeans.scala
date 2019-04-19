package org.renaissance.jdk.concurrent

import org.renaissance.Config
import org.renaissance.License
import org.renaissance.RenaissanceBenchmark

class FJKMeans extends RenaissanceBenchmark {
  def description = "Runs the k-means algorithm using the fork/join framework."

  override def defaultRepetitions = 30

  def licenses = License.create(License.APACHE2)

  private val DIMENSION = 5

  private val VECTOR_LENGTH = 30000

  private val CLUSTER_COUNT = 10

  private val ITERATION_COUNT = 50

  private val THREAD_COUNT = Runtime.getRuntime.availableProcessors

  private var benchmark: KMeansBench = null

  override def setUpBeforeAll(c: Config): Unit = {
    benchmark = new KMeansBench(
      DIMENSION,
      VECTOR_LENGTH,
      CLUSTER_COUNT,
      ITERATION_COUNT,
      THREAD_COUNT
    )
  }

  override def runIteration(c: Config): Unit = {
    benchmark.run
  }
}
