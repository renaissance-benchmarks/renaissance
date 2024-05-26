package org.renaissance.scala.stm

import org.renaissance.Benchmark
import org.renaissance.Benchmark._
import org.renaissance.BenchmarkContext
import org.renaissance.BenchmarkResult
import org.renaissance.BenchmarkResult.Validators
import org.renaissance.License

@Name("scala-stm-bench7")
@Group("scala-stm")
@Group("scala") // With Scala 3, the primary group goes last.
@Summary("Runs the stmbench7 benchmark using ScalaSTM.")
@Licenses(Array(License.BSD3, License.GPL2))
@Repetitions(60)
@Parameter(name = "thread_count", defaultValue = "$cpu.count")
@Configuration(name = "test")
@Configuration(name = "jmh")
final class ScalaStmBench7 extends Benchmark {

  // TODO: Consolidate benchmark parameters across the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/27

  private var stmBenchArgs: Array[String] = _

  override def setUpBeforeAll(c: BenchmarkContext): Unit = {
    val threadCountParam = c.parameter("thread_count").toPositiveInteger

    // The following is the description of STMBench7's arguments.
    // -s -- the initializer class for the STM implementation
    // -g -- the type of synchronization that the benchmark should use
    // -w -- the type of the workload (we use the read/write workload)
    // -c -- the count of operations to execute in the benchmark
    // -t -- the number of threads to use
    stmBenchArgs = Array(
      "-s",
      "stmbench7.scalastm.ScalaSTMInitializer",
      "-g",
      "stm",
      "-w",
      "rw",
      "-c",
      "20",
      "-t",
      threadCountParam.toString
    )
  }

  override def run(c: BenchmarkContext): BenchmarkResult = {
    // TODO: Make the benchmark return something useful
    stmbench7.Benchmark.main(stmBenchArgs)

    // TODO: add proper validation
    Validators.dummy()
  }
}
