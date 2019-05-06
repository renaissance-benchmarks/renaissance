package org.renaissance.rx

import org.renaissance.Config
import org.renaissance.License
import org.renaissance.RenaissanceBenchmark

class RxScrabble extends RenaissanceBenchmark {
  def description = "Solves the Scrabble puzzle using the Rx streams."

  override def defaultRepetitions = 80

  def licenses = License.create(License.GPL2)

  var scrabblePath: String = "/scrabble.txt"

  var shakespearePath: String = "/shakespeare.txt"

  var bench: RxScrabbleImplementation = null

  @volatile var lastResult = 0

  override def setUpBeforeAll(c: Config): Unit = {
    if (c.functionalTest) {
      shakespearePath = "/shakespeare-truncated.txt"
    }
    bench = new RxScrabbleImplementation(scrabblePath, shakespearePath)
  }

  override def runIteration(c: Config): Unit = {
    lastResult = bench.runScrabble().size()
  }
}
