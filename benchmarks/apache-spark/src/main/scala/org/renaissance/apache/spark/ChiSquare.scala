package org.renaissance.apache.spark

import java.nio.charset.StandardCharsets
import java.nio.file.{Path, Paths}

import org.apache.commons.io.FileUtils
import org.apache.commons.io.IOUtils
import org.apache.spark.SparkContext
import org.apache.spark.SparkConf
import org.apache.spark.mllib.linalg.Vectors
import org.apache.spark.mllib.regression.LabeledPoint
import org.apache.spark.mllib.stat.Statistics
import org.apache.spark.mllib.stat.test.ChiSqTestResult
import org.apache.spark.rdd.RDD
import org.renaissance.RenaissanceBenchmark
import org.renaissance.Config
import org.renaissance.License

import scala.util.Random

class ChiSquare extends RenaissanceBenchmark {

  def description = "Runs the chi-square test from Spark MLlib."

  override def defaultRepetitions = 60

  override def licenses = License.create(License.APACHE2)

  val COMPONENTS = 5

  val SIZE = 1500000

  val THREAD_COUNT = Runtime.getRuntime.availableProcessors

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

  def setUpSpark() = {
    val conf = new SparkConf()
      .setAppName("chi-square")
      .setMaster(s"local[$THREAD_COUNT]")
      .set("spark.local.dir", tempDirPath.toString)
    sc = new SparkContext(conf)
    sc.setLogLevel("ERROR")

  }

  override def setUpBeforeAll(c: Config): Unit = {
    tempDirPath = RenaissanceBenchmark.generateTempDir("chi_square")
    setUpSpark()
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
    sc.stop()
    RenaissanceBenchmark.deleteTempDir(tempDirPath)
  }

}
