package org.renaissance.scala.stm

import org.renaissance.BenchmarkResult
import org.renaissance.Config
import org.renaissance.EmptyResult
import org.renaissance.License
import org.renaissance.RenaissanceBenchmark
import org.renaissance.Benchmark._

@Name("philosophers")
@Group("scala-stm")
@Summary("Solves a variant of the dining philosophers problem using ScalaSTM.")
@Licenses(Array(License.BSD3))
@Repetitions(30)
class Philosophers extends RenaissanceBenchmark {

  // TODO: Consolidate benchmark parameters across the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/27

  private val THREAD_COUNT = 8

  /**
   * Number of meals consumed by each Philosopher thread.
   */
  private var NUMBER_OF_MEALS = 500000

  override def setUpBeforeAll(c: Config) = {
    if (c.functionalTest) {
      NUMBER_OF_MEALS = 500
    }
  }

  override def runIteration(c: Config): BenchmarkResult = {
    RealityShowPhilosophers.run(NUMBER_OF_MEALS, THREAD_COUNT)
    // TODO: add proper validation
    return new EmptyResult
  }

}
