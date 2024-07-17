package org.renaissance.scala.stm

import org.renaissance.Benchmark
import org.renaissance.Benchmark._
import org.renaissance.BenchmarkContext
import org.renaissance.BenchmarkResult
import org.renaissance.BenchmarkResult.Assert
import org.renaissance.License

@Name("philosophers")
@Group("scala-stm")
@Group("scala") // With Scala 3, the primary group goes last.
@Summary("Solves a variant of the dining philosophers problem using ScalaSTM.")
@Licenses(Array(License.BSD3))
@Repetitions(30)
@Parameter(name = "thread_count", defaultValue = "$cpu.count")
@Parameter(
  name = "meal_count",
  defaultValue = "500000",
  summary = "Number of meals consumed by each philosopher thread"
)
@Configuration(name = "test", settings = Array("meal_count = 500"))
@Configuration(name = "jmh")
final class Philosophers extends Benchmark {

  // TODO: Consolidate benchmark parameters across the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/27

  private var threadCountParam: Int = _

  /**
   * Number of meals consumed by each Philosopher thread.
   */
  private var mealCountParam: Int = _

  override def setUpBeforeAll(c: BenchmarkContext): Unit = {
    threadCountParam = c.parameter("thread_count").toPositiveInteger
    mealCountParam = c.parameter("meal_count").toPositiveInteger
  }

  private def validate(forkOwners: Seq[Option[String]], mealsEaten: Seq[Int]): Unit = {
    // All forks should be available, i.e., not owned by anyone.
    for (i <- 0 until threadCountParam) {
      Assert.assertEquals(None, forkOwners(i), s"owner of fork %i")
    }

    // All philosophers should have eaten the expected number of meals.
    for (i <- 0 until threadCountParam) {
      Assert.assertEquals(mealCountParam, mealsEaten(i), s"meals eaten by philosopher $i")
    }
  }

  override def run(c: BenchmarkContext): BenchmarkResult = {
    val (forkOwners, mealsEaten) = RealityShowPhilosophers.run(mealCountParam, threadCountParam)

    () => {
      validate(forkOwners, mealsEaten)
    }
  }

}
