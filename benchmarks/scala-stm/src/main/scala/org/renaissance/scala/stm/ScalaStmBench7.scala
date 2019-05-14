package org.renaissance.scala.stm

import org.renaissance.Config
import org.renaissance.License
import org.renaissance.RenaissanceBenchmark
import org.renaissance.Benchmark._

@Name("scala-stm-bench7")
@Group("scala-stm")
@Summary("Runs the stmbench7 benchmark using ScalaSTM.")
@Licenses(Array(License.BSD3, License.GPL2))
@Repetitions(60)
class ScalaStmBench7 extends RenaissanceBenchmark {

  // TODO: Consolidate benchmark parameters across the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/27

  val THREAD_COUNT = Runtime.getRuntime.availableProcessors

  override def runIteration(c: Config): Unit = {
    // The following is the description of STMBench7's arguments.
    // -s -- the initializer class for the STM implementation
    // -g -- the type of synchronization that the benchmark should use
    // -w -- the type of the workload (we use the read/write workload)
    // -c -- the count of operations to execute in the benchmark
    // -t -- the number of threads to use
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

    stmbench7.Benchmark.main(args)
  }
}
