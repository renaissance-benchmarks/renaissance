package org.renaissance.jdk.concurrent

import org.renaissance.Config
import org.renaissance.License
import org.renaissance.RenaissanceBenchmark




class FJKMeans extends RenaissanceBenchmark {
  def description = "Runs the k-means algorithm using the fork/join framework."

  override def defaultRepetitions = 30

  def licenses = License.create(License.APACHE2)

  private val THREAD_COUNT = Runtime.getRuntime.availableProcessors

  private val SIZE = 30000

  override def runIteration(c: Config): Unit = {
    KMeansBench.run(THREAD_COUNT, SIZE)
  }
}