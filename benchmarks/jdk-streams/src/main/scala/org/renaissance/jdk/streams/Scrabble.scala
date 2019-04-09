package org.renaissance.jdk.streams

import org.renaissance.Config
import org.renaissance.RenaissanceBenchmark

class Scrabble extends RenaissanceBenchmark {
  def description = "Solves the Scrabble puzzle using JDK Streams."

  override def defaultRepetitions = 50

  @volatile var lastResult = 0

  override def runIteration(c: Config): Unit = {
    lastResult = JavaScrabble.run()
  }
}
