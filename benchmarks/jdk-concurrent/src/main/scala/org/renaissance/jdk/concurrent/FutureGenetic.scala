package org.renaissance.jdk.concurrent

import org.renaissance.Config
import org.renaissance.License
import org.renaissance.RenaissanceBenchmark

class FutureGenetic extends RenaissanceBenchmark {
  def description = "Runs a genetic algorithm using the Jenetics library and futures."

  override def defaultRepetitions = 50

  def licenses = License.create(License.APACHE2)

  // TODO: Consolidate benchmark parameters across the suite.
  //  See: https://github.com/D-iii-S/renaissance-benchmarks/issues/27
  val threadCount = 2

  val randomSeed = 7

  var geneMinValue = -2000

  var geneMaxValue = 2000

  var geneCount = 200

  var chromosomeCount = 50

  var generationCount = 5000

  var benchmark: JavaJenetics = null

  override def setUpBeforeAll(c: Config): Unit = {
    if (c.functionalTest) {
      chromosomeCount = 10
      generationCount = 200
    }
    benchmark = new JavaJenetics(
      geneMinValue,
      geneMaxValue,
      geneCount,
      chromosomeCount,
      generationCount,
      threadCount,
      randomSeed
    )
    benchmark.setupBeforeAll()
  }

  override def tearDownAfterAll(c: Config): Unit = {
    benchmark.tearDownAfterAll()
  }

  override def runIteration(c: Config): Unit = {
    blackHole(benchmark.runRepetition())
  }
}
