package org.renaissance.apache.spark

import java.nio.charset.Charset
import java.nio.file.Path
import java.nio.file.Paths

import org.apache.commons.io.FileUtils
import org.apache.spark.SparkContext
import org.apache.spark.mllib.recommendation.MatrixFactorizationModel
import org.apache.spark.mllib.recommendation.Rating
import org.apache.spark.rdd.RDD
import org.renaissance.Benchmark
import org.renaissance.Benchmark._
import org.renaissance.BenchmarkContext
import org.renaissance.BenchmarkResult
import org.renaissance.License

import scala.util.Random

@Name("als")
@Group("apache-spark")
@Summary("Runs the ALS algorithm from the Spark MLlib.")
@Licenses(Array(License.APACHE2))
@Repetitions(30)
@Parameter(name = "rating_count", defaultValue = "20000")
// Work around @Repeatable annotations not working in this Scala version.
@Configurations(
  Array(
    new Configuration(name = "test", settings = Array("rating_count = 500")),
    new Configuration(name = "jmh")
  )
)
final class Als extends Benchmark with SparkUtil {

  // TODO: Consolidate benchmark parameters across the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/27

  private var ratingCountParam: Int = _

  private val THREAD_COUNT = 4

  // TODO: Unify handling of scratch directories throughout the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/13

  val alsPath = Paths.get("target", "als")

  val outputPath = alsPath.resolve("output")

  val bigInputFile = alsPath.resolve("bigfile.txt")

  var sc: SparkContext = _

  var factModel: MatrixFactorizationModel = _

  var ratings: RDD[Rating] = _

  var tempDirPath: Path = _

  def prepareInput() = {
    FileUtils.deleteDirectory(alsPath.toFile)
    val rand = new Random
    val lines = (0 until ratingCountParam).flatMap { user =>
      (0 until 100).map { product =>
        val score = 1 + rand.nextInt(3) + rand.nextInt(3)
        s"$user::$product::$score"
      }
    }
    FileUtils.write(bigInputFile.toFile, lines.mkString("\n"), Charset.defaultCharset(), true)
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

  override def setUpBeforeAll(c: BenchmarkContext): Unit = {
    ratingCountParam = c.intParameter("rating_count")

    tempDirPath = c.generateTempDir("als")
    sc = setUpSparkContext(tempDirPath, THREAD_COUNT, "als")
    prepareInput()
    loadData()
  }

  override def tearDownAfterAll(c: BenchmarkContext): Unit = {
    // Dump output.
    factModel.userFeatures
      .map {
        case (user, features) => s"$user: ${features.mkString(", ")}"
      }
      .saveAsTextFile(outputPath.toString)

    tearDownSparkContext(sc)
    c.deleteTempDir(tempDirPath)
  }

  override def runIteration(c: BenchmarkContext): BenchmarkResult = {
    val als = new org.apache.spark.mllib.recommendation.ALS()
    factModel = als.run(ratings)

    // TODO: add proper validation of the generated model
    BenchmarkResult.dummy(factModel)
  }
}
