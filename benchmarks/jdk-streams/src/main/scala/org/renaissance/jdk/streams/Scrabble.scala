package org.renaissance.jdk.streams

import org.renaissance.Benchmark
import org.renaissance.Benchmark._
import org.renaissance.BenchmarkContext
import org.renaissance.BenchmarkResult
import org.renaissance.License
import org.renaissance.ValidationException

import scala.collection.JavaConverters

@Name("scrabble")
@Group("jdk-streams")
@Summary("Solves the Scrabble puzzle using JDK Streams.")
@Licenses(Array(License.GPL2))
@Repetitions(50)
class Scrabble extends Benchmark {

  // TODO: Consolidate benchmark parameters across the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/27

  var shakespearePath = "/shakespeare.txt"

  var scrabblePath = "/scrabble.txt"

  var scrabble: JavaScrabble = null

  val expectedResultFull = Seq("120--QUICKLY", "118--ZEPHYRS", "114--QUALIFY-QUICKEN-QUICKER")
  val expectedResultTest = Seq("120--QUICKLY", "114--QUICKEN-QUICKER", "108--BLAZING-PRIZING")

  override def setUpBeforeAll(c: BenchmarkContext): Unit = {
    if (c.functionalTest) {
      shakespearePath = "/shakespeare-truncated.txt"
    }
    scrabble = new JavaScrabble(shakespearePath, scrabblePath)
  }

  override def runIteration(c: BenchmarkContext): BenchmarkResult = {
    val result = scrabble.run()
    val expected = if (c.functionalTest) expectedResultTest else expectedResultFull

    () => {
      val actualWords = JavaScrabble.prepareForValidation(result)
      ValidationException.throwIfNotEqual(expected.size, actualWords.size, "best words count")

      for ((expected, actual) <- expected zip JavaConverters.asScalaBuffer(actualWords)) {
        ValidationException.throwIfNotEqual(expected, actual, "best words")
      }
    }
  }
}
