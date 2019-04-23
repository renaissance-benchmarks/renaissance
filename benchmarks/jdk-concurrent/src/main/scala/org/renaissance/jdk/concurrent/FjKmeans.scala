package org.renaissance.jdk.concurrent

import org.renaissance.Config
import org.renaissance.License
import org.renaissance.RenaissanceBenchmark

class FjKmeans extends RenaissanceBenchmark {
  override def description = "Runs the k-means algorithm using the Fork/Join framework."

  override def licenses = License.create(License.GPL2)

  override def defaultRepetitions = 30

  // TODO: Consolidate benchmark parameters across the suite.
  //  See: https://github.com/D-iii-S/renaissance-benchmarks/issues/27
  private val THREAD_COUNT = Runtime.getRuntime.availableProcessors

  private val SIZE = 30000

  protected override def runIteration(config: Config): Unit = {
    KMeansBench.run(THREAD_COUNT, SIZE)
  }
}
