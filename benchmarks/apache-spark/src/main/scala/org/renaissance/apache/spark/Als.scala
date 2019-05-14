package org.renaissance.apache.spark

import java.nio.file.Path
import java.nio.file.Paths

import org.apache.commons.io.FileUtils
import org.apache.spark.SparkContext
import org.apache.spark.mllib.recommendation.MatrixFactorizationModel
import org.apache.spark.mllib.recommendation.Rating
import org.apache.spark.rdd.RDD
import org.renaissance.Config
import org.renaissance.License
import org.renaissance.RenaissanceBenchmark
import org.renaissance.Benchmark._

import scala.util.Random

@Summary("Runs the ALS algorithm from the Spark MLlib.")
@Licenses(Array(License.APACHE2))
@Repetitions(60)
class Als extends RenaissanceBenchmark with SparkUtil {

  // TODO: Consolidate benchmark parameters across the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/27

  var numRatings = 20000

  val THREAD_COUNT = Runtime.getRuntime.availableProcessors

  // TODO: Unify handling of scratch directories throughout the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/13

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
    val lines = (0 until numRatings).flatMap { user =>
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

  override def setUpBeforeAll(c: Config): Unit = {
    tempDirPath = RenaissanceBenchmark.generateTempDir("als")
    sc = setUpSparkContext(tempDirPath, THREAD_COUNT)
    if (c.functionalTest) {
      numRatings = 500
    }
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

    tearDownSparkContext(sc)
    RenaissanceBenchmark.deleteTempDir(tempDirPath)
  }

  def runIteration(c: Config): Unit = {
    val als = new org.apache.spark.mllib.recommendation.ALS()
    factModel = als.run(ratings)
  }
}
