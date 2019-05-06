package org.renaissance.jdk.streams

import org.renaissance.Config
import org.renaissance.License
import org.renaissance.RenaissanceBenchmark

class Scrabble extends RenaissanceBenchmark {
  def description = "Solves the Scrabble puzzle using JDK Streams."

  override def defaultRepetitions = 50

  def licenses = License.create(License.GPL2)

  var shakespearePath = "/shakespeare.txt"

  var scrabblePath = "/scrabble.txt"

  var scrabble: JavaScrabble = null

  override def setUpBeforeAll(c: Config): Unit = {
    if (c.functionalTest) {
      shakespearePath = "/shakespeare-truncated.txt"
    }
    scrabble = new JavaScrabble(shakespearePath, scrabblePath)
  }

  override def runIteration(c: Config): Unit = {
    blackHole(scrabble.run())
  }
}
