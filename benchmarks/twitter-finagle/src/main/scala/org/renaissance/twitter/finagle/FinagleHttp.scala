package org.renaissance.twitter.finagle

import org.renaissance.Config
import org.renaissance.License
import org.renaissance.RenaissanceBenchmark

class FinagleHttp extends RenaissanceBenchmark {
  def description = "Sends many small Finagle HTTP requests and awaits the response."

  override def defaultRepetitions = 12

  def licenses = License.create(License.APACHE2)

  override def runIteration(c: Config): Unit = {}
}
