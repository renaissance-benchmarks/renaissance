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
@Parameter(
  name = "block_meal_count",
  defaultValue = "4096",
  summary =
    "Number of meals representing a block of progress. Determines determines the frequency of camera scans. Must be a power of two."
)
@Configuration(name = "test", settings = Array("meal_count = 500", "block_meal_count = 8"))
@Configuration(name = "jmh")
final class Philosophers extends Benchmark {

  // TODO: Consolidate benchmark parameters across the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/27

  private var threadCountParam: Int = _

  /** Number of meals consumed by each Philosopher thread. */
  private var mealCountParam: Int = _

  /**
   * Number of meals representing a block of progress which determines
   * the frequency of camera scans. Must be power of two to enable
   * efficient checking.
   */
  private var blockMealCountParam: Int = _

  override def setUpBeforeAll(c: BenchmarkContext): Unit = {
    def isPowerOfTwo(n: Int): Boolean = if (n <= 0) false else (n & (n - 1)) == 0

    threadCountParam = c.parameter("thread_count").toPositiveInteger
    mealCountParam = c.parameter("meal_count").toPositiveInteger

    blockMealCountParam = c.parameter("block_meal_count").toPositiveInteger
    if (!isPowerOfTwo(blockMealCountParam)) {
      throw new IllegalArgumentException(
        s"the 'block_meal_count' parameter is not a power of two: $blockMealCountParam"
      )
    }
  }

  private def validate(result: (Seq[Option[String]], Seq[Int], Int)): Unit = {
    val (forkOwners, mealsEaten, scanCount) = result

    // All forks should be available, i.e., not owned by anyone.
    for (i <- 0 until threadCountParam) {
      Assert.assertEquals(None, forkOwners(i), s"owner of fork %i")
    }

    // All philosophers should have eaten the expected number of meals.
    for (i <- 0 until threadCountParam) {
      Assert.assertEquals(mealCountParam, mealsEaten(i), s"meals eaten by philosopher $i")
    }

    // The camera performed the expected number of scans.
    val expectedScanCount = mealCountParam / blockMealCountParam
    Assert.assertEquals(expectedScanCount, scanCount, "camera scans")
  }

  override def run(c: BenchmarkContext): BenchmarkResult = {
    val result = RealityShowPhilosophers.run(
      mealCountParam,
      threadCountParam,
      blockMealCountParam
    )

    () => {
      validate(result)
    }
  }

}
