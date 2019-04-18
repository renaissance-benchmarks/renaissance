package org.renaissance.apache.spark

import java.io._
import java.nio.charset.StandardCharsets
import java.nio.file.{Path, Paths}
import java.util.zip._

import org.apache.commons.io.FileUtils
import org.apache.commons.io.IOUtils
import org.apache.spark.SparkContext
import org.apache.spark.SparkConf
import org.apache.spark.mllib.linalg.Vectors
import org.apache.spark.mllib.clustering.GaussianMixture
import org.apache.spark.mllib.clustering.GaussianMixtureModel
import org.apache.spark.rdd.RDD

import scala.util.Random
import org.renaissance.{Config, License, RenaissanceBenchmark}

class GaussMix extends RenaissanceBenchmark {

  /* TODO Implement changes regarding how to declare and pass
  benchmark-specific parameters
  ( see https://github.com/D-iii-S/renaissance-benchmarks/issues/27)
   */

  def description = "Computes a Gaussian mixture model using expectation-maximization."

  override def defaultRepetitions = 40

  override def licenses = License.create(License.APACHE2)

  val DISTRIBUTION_COUNT = 6

  val COMPONENTS = 10

  val THREAD_COUNT = Runtime.getRuntime.availableProcessors

  val SIZE = 15000

  val gaussMixPath = Paths.get("target", "gauss-mix")

  val outputPath = gaussMixPath.resolve("output")

  val measurementsFile = gaussMixPath.resolve("measurements.txt")

  var sc: SparkContext = null

  var gmm: GaussianMixtureModel = null

  var input: RDD[org.apache.spark.mllib.linalg.Vector] = null

  var tempDirPath: Path = null

  override def setUpBeforeAll(c: Config): Unit = {
    tempDirPath = RenaissanceBenchmark.generateTempDir("gauss_mix")
    setUpSpark()
    prepareInput()
    loadData()
  }

  def setUpSpark() = {
    val conf = new SparkConf()
      .setAppName("gauss-mix")
      .setMaster(s"local[$THREAD_COUNT]")
      .set("spark.local.dir", tempDirPath.toString)
    sc = new SparkContext(conf)
    sc.setLogLevel("ERROR")
  }

  def prepareInput() = {
    FileUtils.deleteDirectory(gaussMixPath.toFile)
    val rand = new Random(0L)
    val content = new StringBuilder
    for (i <- 0 until SIZE) {
      def randDouble(): Double = {
        (rand.nextDouble() * 10).toInt / 10.0
      }
      content.append((0 until COMPONENTS).map(_ => randDouble()).mkString(" "))
      content.append("\n")
    }
    FileUtils.write(measurementsFile.toFile, content, StandardCharsets.UTF_8, true)
  }

  def loadData() : Unit = {
    input = sc
      .textFile(measurementsFile.toString)
      .map { line =>
        val raw = line.split(" ").map(_.toDouble)
        Vectors.dense(raw)
      }
      .cache()
  }

  override def tearDownAfterAll(c: Config) = {
    val output = gmm.gaussians.mkString(", ")
    FileUtils.write(outputPath.toFile, output, StandardCharsets.UTF_8, true)
    sc.stop()
    RenaissanceBenchmark.deleteTempDir(tempDirPath)
  }

  override def runIteration(c: Config): Unit = {
    gmm = new GaussianMixture()
      .setK(DISTRIBUTION_COUNT)
      .setMaxIterations(15)
      .run(input)
  }

}
