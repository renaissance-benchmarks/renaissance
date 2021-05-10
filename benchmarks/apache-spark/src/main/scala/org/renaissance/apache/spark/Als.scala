package org.renaissance.apache.spark

import org.apache.spark.mllib.recommendation.MatrixFactorizationModel
import org.apache.spark.mllib.recommendation.Rating
import org.apache.spark.rdd.RDD
import org.renaissance.Benchmark
import org.renaissance.Benchmark._
import org.renaissance.BenchmarkContext
import org.renaissance.BenchmarkResult
import org.renaissance.BenchmarkResult.Validators
import org.renaissance.License

import java.nio.file.Files
import java.nio.file.Path
import scala.jdk.CollectionConverters.asJavaCollectionConverter
import scala.util.Random

@Name("als")
@Group("apache-spark")
@Summary("Runs the ALS algorithm from the Spark MLlib.")
@Licenses(Array(License.APACHE2))
@Repetitions(30)
@Parameter(
  name = "spark_executor_count",
  defaultValue = "4",
  summary = "Number of executor instances."
)
@Parameter(
  name = "spark_executor_thread_count",
  defaultValue = "4",
  summary = "Number of threads per executor."
)
@Parameter(
  name = "user_count",
  defaultValue = "20000",
  summary = "Number of users giving ratings."
)
@Parameter(
  name = "product_count",
  defaultValue = "100",
  summary = "Number of products rated by each user."
)
@Configuration(name = "test", settings = Array("user_count = 500"))
@Configuration(name = "jmh")
final class Als extends Benchmark with SparkUtil {

  // TODO: Consolidate benchmark parameters across the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/27

  private val randomSeed = 17

  private var inputRatings: RDD[Rating] = _

  private var outputMatrixFactorization: MatrixFactorizationModel = _

  private def prepareInput(userCount: Int, productCount: Int, outputFile: Path): Path = {
    // TODO: Use a Renaissance-provided random generator.
    val rand = new Random(randomSeed)
    val lines = (0 until userCount).flatMap { user =>
      (0 until productCount).map { product =>
        val score = 1 + rand.nextInt(3) + rand.nextInt(3)
        s"$user::$product::$score"
      }
    }

    // Write output using UTF-8 encoding.
    Files.write(outputFile, lines.asJavaCollection)
  }

  private def loadData(inputFile: Path) = {
    sparkContext
      .textFile(inputFile.toString)
      .map { line =>
        val parts = line.split("::")
        Rating(parts(0).toInt, parts(1).toInt, parts(2).toDouble)
      }
      .cache()
  }

  override def setUpBeforeAll(bc: BenchmarkContext): Unit = {
    setUpSparkContext(bc)

    val inputFile = prepareInput(
      bc.parameter("user_count").toPositiveInteger,
      bc.parameter("product_count").toPositiveInteger,
      bc.scratchDirectory().resolve("input.txt")
    )

    inputRatings = ensureCached(loadData(inputFile))
  }

  override def run(bc: BenchmarkContext): BenchmarkResult = {
    val als = new org.apache.spark.mllib.recommendation.ALS()
    outputMatrixFactorization = als.run(inputRatings)

    // TODO: add proper validation of the generated model
    Validators.dummy(outputMatrixFactorization)
  }

  override def tearDownAfterAll(bc: BenchmarkContext): Unit = {
    val outputPath = bc.scratchDirectory().resolve("output")
    dumpResult(outputMatrixFactorization, outputPath)

    tearDownSparkContext()
  }

  private def dumpResult(mfm: MatrixFactorizationModel, outputPath: Path) = {
    mfm.userFeatures
      .map {
        case (user, features) => s"$user: ${features.mkString(", ")}"
      }
      .saveAsTextFile(outputPath.toString)
  }
}
