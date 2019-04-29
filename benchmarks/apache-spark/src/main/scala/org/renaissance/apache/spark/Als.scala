package org.renaissance.apache.spark

import java.nio.file.{Path, Paths}

import org.apache.commons.io.FileUtils
import org.apache.spark.SparkConf
import org.apache.spark.SparkContext
import org.apache.spark.mllib.recommendation.MatrixFactorizationModel
import org.apache.spark.mllib.recommendation.Rating
import org.apache.spark.rdd.RDD
import org.renaissance.{Config, License, RenaissanceBenchmark}

import scala.util.Random

class Als extends RenaissanceBenchmark {

  override def description(): String = "Runs the ALS algorithm from the Spark MLlib."

  override def defaultRepetitions = 60

  override def licenses(): Array[License] = License.create(License.APACHE2)

  // TODO: Consolidate benchmark parameters across the suite.
  //  See: https://github.com/D-iii-S/renaissance-benchmarks/issues/27

  val THREAD_COUNT = Runtime.getRuntime.availableProcessors

  // TODO: Consolidate paths to avoid clashes between parallel executions
  // https://github.com/D-iii-S/renaissance-benchmarks/issues/13

  val alsPath = Paths.get("target", "als")

  val outputPath = alsPath.resolve("output")

  val bigInputFile = alsPath.resolve("bigfile.txt")

  var sc: SparkContext = null

  var factModel: MatrixFactorizationModel = null

  var ratings: RDD[Rating] = null

  var tempDirPath: Path = null

  def prepareInput() = {
    FileUtils.deleteDirectory(alsPath.toFile)
    val rand = new Random
    val lines = (0 until 20000).flatMap { user =>
      (0 until 100).map { product =>
        val score = 1 + rand.nextInt(3) + rand.nextInt(3)
        s"$user::$product::$score"
      }
    }
    FileUtils.write(bigInputFile.toFile, lines.mkString("\n"), true)
  }

  def loadData() = {
    ratings = sc
      .textFile(bigInputFile.toString)
      .map { line =>
        val parts = line.split("::")
        Rating(parts(0).toInt, parts(1).toInt, parts(2).toDouble)
      }
      .cache()
  }

  def setUpSpark() = {
    val conf = new SparkConf()
      .setAppName("als")
      .setMaster(s"local[$THREAD_COUNT]")
      .set("spark.local.dir", tempDirPath.toString)
      .set("spark.sql.warehouse.dir", tempDirPath.resolve("warehouse").toString)
    sc = new SparkContext(conf)
    sc.setLogLevel("ERROR")
  }

  override def setUpBeforeAll(c: Config): Unit = {
    tempDirPath = RenaissanceBenchmark.generateTempDir("als")
    setUpSpark()
    prepareInput()
    loadData()
  }

  override def tearDownAfterAll(c: Config): Unit = {
    // Dump output.
    factModel.userFeatures
      .map {
        case (user, features) => s"$user: ${features.mkString(", ")}"
      }
      .saveAsTextFile(outputPath.toString)

    sc.stop()
    RenaissanceBenchmark.deleteTempDir(tempDirPath)
  }

  def runIteration(c: Config): Unit = {
    val als = new org.apache.spark.mllib.recommendation.ALS()
    factModel = als.run(ratings)
  }
}
