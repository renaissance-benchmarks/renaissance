package org.renaissance.apache.spark

import java.io.File
import java.nio.charset.StandardCharsets
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

  val chiSquarePath = "target/chi-square"

  val outputPath = chiSquarePath + "/output"

  val bigInputFile = chiSquarePath + "/measurements.txt"

  var sc: SparkContext = null

  var input: RDD[LabeledPoint] = null

  var results: Array[ChiSqTestResult] = null

  override def setUpBeforeAll(c: Config): Unit = {
    val conf = new SparkConf()
      .setAppName("chi-square")
      .setMaster(s"local[$THREAD_COUNT]")
      .set("spark.local.dir", "_tmp")
    sc = new SparkContext(conf)
    sc.setLogLevel("ERROR")

    // Prepare input.
    FileUtils.deleteDirectory(new File(chiSquarePath))
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

    FileUtils.write(new File(bigInputFile), content, StandardCharsets.UTF_8, true)

    // Load data.
    input = sc
      .textFile(bigInputFile)
      .map { line =>
        val raw = line.split(" ").map(_.toDouble)
        new LabeledPoint(raw.head, Vectors.dense(raw.tail))
      }
  }

  override def runIteration(c: Config): Unit = {
    results = Statistics.chiSqTest(input)
  }

  override def tearDownAfterAll(c: Config): Unit = {

    FileUtils.write(
      new File(outputPath),
      results.map(_.statistic).mkString(", "),
      StandardCharsets.UTF_8,
      true
    )

    sc.stop()
  }

}
