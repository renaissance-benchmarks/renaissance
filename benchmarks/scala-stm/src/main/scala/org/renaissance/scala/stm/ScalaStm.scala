package org.renaissance.scala.stm

import org.renaissance.Config
import org.renaissance.License
import org.renaissance.RenaissanceBenchmark

class ScalaStm extends RenaissanceBenchmark {
  def description = "Solves the Scrabble puzzle using JDK Streams."

  override def defaultRepetitions = 50

  def licenses = License.create(License.BSD3, License.GPL2)

  override def runIteration(c: Config): Unit = {}
}
