package org.renaissance.scala.stm

import org.renaissance.Benchmark._
import org.renaissance.{Config, License, RenaissanceBenchmark}

class Philosophers extends RenaissanceBenchmark {

  override def description(): String =
    "Solves a variant of the dining philosophers problem using ScalaSTM."

  override def defaultRepetitions = 30

  def licenses = License.create(License.BSD3)

  // TODO: Consolidate benchmark parameters across the suite.
  //  See: https://github.com/D-iii-S/renaissance-benchmarks/issues/27
  private val THREAD_COUNT = Runtime.getRuntime.availableProcessors

  /**
   * Number of meals consumed by each Philosopher thread.
   */
  private var NUMBER_OF_MEALS = 500000

  override def setUpBeforeAll(c: Config) = {
    if (c.functionalTest) {
      NUMBER_OF_MEALS = 500
    }
  }

  override def runIteration(c: Config): Unit = {
    RealityShowPhilosophers.run(NUMBER_OF_MEALS, THREAD_COUNT)
  }

}
