package org.renaissance.scala.stm

import org.renaissance.Benchmark
import org.renaissance.Benchmark._
import org.renaissance.BenchmarkContext
import org.renaissance.BenchmarkResult
import org.renaissance.License

@Name("philosophers")
@Group("scala-stm")
@Summary("Solves a variant of the dining philosophers problem using ScalaSTM.")
@Licenses(Array(License.BSD3))
@Repetitions(30)
// Work around @Repeatable annotations not working in this Scala version.
@Parameters(
  Array(
    new Parameter(name = "thread_count", defaultValue = "$cpu.count"),
    new Parameter(
      name = "meal_count",
      defaultValue = "500000",
      summary = "Number of meals consumed by each philosopher thread"
    )
  )
)
@Configurations(
  Array(
    new Configuration(name = "test", settings = Array("meal_count = 500")),
    new Configuration(name = "jmh")
  )
)
final class Philosophers extends Benchmark {

  // TODO: Consolidate benchmark parameters across the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/27

  private var threadCountParam: Int = _

  /**
   * Number of meals consumed by each Philosopher thread.
   */
  private var mealCountParam: Int = _

  override def setUpBeforeAll(c: BenchmarkContext) = {
    threadCountParam = c.intParameter("thread_count")
    mealCountParam = c.intParameter("meal_count")
  }

  override def runIteration(c: BenchmarkContext): BenchmarkResult = {
    // TODO: Return something useful, not elapsed time
    RealityShowPhilosophers.run(mealCountParam, threadCountParam)

    // TODO: add proper validation
    BenchmarkResult.dummy()
  }

}
