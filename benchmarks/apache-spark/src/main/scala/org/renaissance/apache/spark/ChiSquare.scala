package org.renaissance.apache.spark

import java.nio.charset.StandardCharsets
import java.nio.file.Paths

import org.apache.commons.io.FileUtils
import org.apache.spark.SparkContext
import org.apache.spark.mllib.linalg.Vectors
import org.apache.spark.mllib.regression.LabeledPoint
import org.apache.spark.mllib.stat.Statistics
import org.apache.spark.mllib.stat.test.ChiSqTestResult
import org.apache.spark.rdd.RDD
import org.renaissance.Benchmark
import org.renaissance.Benchmark._
import org.renaissance.BenchmarkContext
import org.renaissance.BenchmarkResult
import org.renaissance.BenchmarkResult.Validators
import org.renaissance.License

import scala.util.Random

@Name("chi-square")
@Group("apache-spark")
@Summary("Runs the chi-square test from Spark MLlib.")
@Licenses(Array(License.APACHE2))
@Repetitions(60)
@Parameter(name = "thread_count", defaultValue = "$cpu.count")
@Parameter(name = "number_count", defaultValue = "1500000")
@Configuration(name = "test", settings = Array("number_count = 10000"))
@Configuration(name = "jmh")
final class ChiSquare extends Benchmark with SparkUtil {

  // TODO: Consolidate benchmark parameters across the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/27

  private var numberCountParam: Int = _

  private var threadCountParam: Int = _

  private val COMPONENTS = 5

  val chiSquarePath = Paths.get("target", "chi-square")

  val outputPath = chiSquarePath.resolve("output")

  val measurementsFile = chiSquarePath.resolve("measurements.txt")

  var sc: SparkContext = _

  var input: RDD[LabeledPoint] = _

  var results: Array[ChiSqTestResult] = _

  def prepareInput() = {
    FileUtils.deleteDirectory(chiSquarePath.toFile)

    val rand = new Random(0L)
    val content = new StringBuilder
    for (i <- 0 until numberCountParam) {
      def randDouble(): Double = {
        (rand.nextDouble() * 10).toInt / 10.0
      }
      content.append(rand.nextInt(2) + " ")
      content.append((0 until COMPONENTS).map(_ => randDouble()).mkString(" "))
      content.append("\n")
    }

    FileUtils.write(measurementsFile.toFile, content, StandardCharsets.UTF_8, true)
  }

  def loadData() = {
    input = sc
      .textFile(measurementsFile.toString)
      .map { line =>
        val raw = line.split(" ").map(_.toDouble)
        new LabeledPoint(raw.head, Vectors.dense(raw.tail))
      }
      .cache()
  }

  override def setUpBeforeAll(c: BenchmarkContext): Unit = {
    threadCountParam = c.parameter("thread_count").toPositiveInteger
    numberCountParam = c.parameter("number_count").toPositiveInteger

    val tempDirPath = c.scratchDirectory()
    sc = setUpSparkContext(tempDirPath, threadCountParam)
    prepareInput()
    loadData()
    ensureCaching(input)
  }

  override def run(c: BenchmarkContext): BenchmarkResult = {
    results = Statistics.chiSqTest(input)

    // TODO: add more sophisticated validation
    Validators.simple("component count", COMPONENTS, results.size)
  }

  override def tearDownAfterAll(c: BenchmarkContext): Unit = {
    val output = results.map(_.statistic).mkString(", ")
    FileUtils.write(outputPath.toFile, output, StandardCharsets.UTF_8, true)
    tearDownSparkContext(sc)
  }

}
