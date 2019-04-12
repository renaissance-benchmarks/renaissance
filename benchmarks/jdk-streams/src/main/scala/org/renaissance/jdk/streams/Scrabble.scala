package org.renaissance.jdk.streams

import org.renaissance.Config
import org.renaissance.License
import org.renaissance.RenaissanceBenchmark

class Scrabble extends RenaissanceBenchmark {
  def description = "Solves the Scrabble puzzle using JDK Streams."

  override def defaultRepetitions = 50

  def licenses = License.create(License.GPL2)

  override def runIteration(c: Config): Unit = {
    blackHole(JavaScrabble.run())
  }
}
