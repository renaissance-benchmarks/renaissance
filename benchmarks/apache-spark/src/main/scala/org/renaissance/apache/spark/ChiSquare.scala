package org.renaissance.apache.spark

import java.nio.charset.StandardCharsets
import java.nio.file.Path
import java.nio.file.Paths

import org.apache.commons.io.FileUtils
import org.apache.spark.SparkContext
import org.apache.spark.mllib.linalg.Vectors
import org.apache.spark.mllib.regression.LabeledPoint
import org.apache.spark.mllib.stat.Statistics
import org.apache.spark.mllib.stat.test.ChiSqTestResult
import org.apache.spark.rdd.RDD
import org.renaissance.Config
import org.renaissance.License
import org.renaissance.RenaissanceBenchmark
import org.renaissance.Benchmark._

import scala.util.Random

@Name("chi-square")
@Group("apache-spark")
@Summary("Runs the chi-square test from Spark MLlib.")
@Licenses(Array(License.APACHE2))
@Repetitions(60)
class ChiSquare extends RenaissanceBenchmark with SparkUtil {

  // TODO: Consolidate benchmark parameters across the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/27

  val COMPONENTS = 5

  var SIZE = 1500000

  // TODO: Unify handling of scratch directories throughout the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/13

  val chiSquarePath = Paths.get("target", "chi-square")

  val outputPath = chiSquarePath.resolve("output")

  val measurementsFile = chiSquarePath.resolve("measurements.txt")

  var tempDirPath: Path = null

  var sc: SparkContext = null

  var input: RDD[LabeledPoint] = null

  var results: Array[ChiSqTestResult] = null

  def prepareInput() = {
    FileUtils.deleteDirectory(chiSquarePath.toFile)
    val rand = new Random(0L)
    val content = new StringBuilder
    for (i <- 0 until SIZE) {
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

  override def setUpBeforeAll(c: Config): Unit = {
    tempDirPath = RenaissanceBenchmark.generateTempDir("chi_square")
    sc = setUpSparkContext(tempDirPath)
    if (c.functionalTest) {
      SIZE = 10000
    }
    prepareInput()
    loadData()
  }

  override def runIteration(c: Config): Unit = {
    results = Statistics.chiSqTest(input)
    blackHole(results)
  }

  override def tearDownAfterAll(c: Config): Unit = {
    val output = results.map(_.statistic).mkString(", ")
    FileUtils.write(outputPath.toFile, output, StandardCharsets.UTF_8, true)
    tearDownSparkContext(sc)
    RenaissanceBenchmark.deleteTempDir(tempDirPath)
  }

}
