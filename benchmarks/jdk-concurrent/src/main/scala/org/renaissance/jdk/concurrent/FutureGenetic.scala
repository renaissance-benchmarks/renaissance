package org.renaissance.jdk.concurrent


import org.renaissance.Config
import org.renaissance.License
import org.renaissance.RenaissanceBenchmark


class FutureGenetic extends RenaissanceBenchmark {
  def description = "Runs a genetic algorithm using the Jenetics library and futures."

  override def defaultRepetitions = 50

  def licenses = License.create(License.APACHE2)

  val benchmark = new JavaJenetics()

  override def setUpBeforeAll(c: Config): Unit = {
    benchmark.setupBeforeAll()
  }

  override def tearDownAfterAll(c: Config): Unit = {
    benchmark.tearDownAfterAll()
  }

  override def runIteration(c: Config): Unit = {
    blackHole(benchmark.runIteration())
  }
}



