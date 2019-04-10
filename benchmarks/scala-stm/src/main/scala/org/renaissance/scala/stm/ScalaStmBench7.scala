package org.renaissance.scala.stm

import org.renaissance.Config
import org.renaissance.License
import org.renaissance.RenaissanceBenchmark
import stmbench7.Benchmark

class ScalaStmBench7 extends RenaissanceBenchmark {
  def description = "Runs the stmbench7 benchmark using ScalaSTM."

  override def defaultRepetitions = 60

  def licenses = License.create(License.BSD3, License.GPL2)

  val THREAD_COUNT = Runtime.getRuntime.availableProcessors

  override def runIteration(c: Config): Unit = {
    val args = Array(
      "-s",
      "stmbench7.scalastm.ScalaSTMInitializer",
      "-g",
      "stm",
      "-w",
      "rw",
      "-c",
      "20",
      "-t",
      THREAD_COUNT.toString
    )
    Benchmark.main(args)
  }
}
