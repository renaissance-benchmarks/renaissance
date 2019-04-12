package org.renaissance.rx

import org.renaissance.Config
import org.renaissance.License
import org.renaissance.RenaissanceBenchmark

class RxScrabble extends RenaissanceBenchmark {
  def description = "Solves the Scrabble puzzle using the Rx streams."

  override def defaultRepetitions = 80

  def licenses = License.create(License.GPL2)

  var bench: RxScrabbleImplementation = null

  @volatile var lastResult = 0

  override def setUpBeforeAll(c: Config): Unit = {
    bench = new RxScrabbleImplementation
  }

  override def runIteration(c: Config): Unit = {
    lastResult = bench.runScrabble().size()
  }
}
