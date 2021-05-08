package org.renaissance.apache.spark

import org.apache.spark.mllib.recommendation.ALS
import org.apache.spark.mllib.recommendation.MatrixFactorizationModel
import org.apache.spark.mllib.recommendation.Rating
import org.apache.spark.rdd.RDD
import org.apache.spark.storage.StorageLevel
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
@Parameter(name = "als_rank", defaultValue = "10")
@Parameter(name = "als_lambda", defaultValue = "0.01")
@Parameter(name = "als_iterations", defaultValue = "10")
@Configuration(name = "test", settings = Array("user_count = 500"))
@Configuration(name = "jmh")
final class Als extends Benchmark with SparkUtil {

  // TODO: Consolidate benchmark parameters across the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/27

  private val randomSeed = 17

  private var alsRankParam: Int = _

  private var alsLambdaParam: Double = _

  private var alsIterationsParam: Int = _

  private var inputRatings: RDD[Rating] = _

  private var outputMatrixFactorization: MatrixFactorizationModel = _

  private def generateRatings(userCount: Int, productCount: Int): Seq[Rating] = {
    // TODO: Use a Renaissance-provided random generator.
    val rand = new Random(randomSeed)

    for (userId <- 0 until userCount; productId <- 0 until productCount) yield {
      val rating = 1 + rand.nextInt(3) + rand.nextInt(3)
      Rating(userId, productId, rating)
    }
  }

  private def storeRatings(ratings: Seq[Rating], file: Path): Path = {
    val lines = ratings.map(r => Rating.unapply(r).get.productIterator.mkString(","))
    Files.write(file, lines.asJavaCollection)
  }

  private def loadRatings(file: Path, partitionCount: Int) = {
    createRddFromCsv(
      file,
      header = false,
      delimiter = ",",
      parts => {
        val (user, product, rating) = (parts(0), parts(1), parts(2))
        Rating(user.toInt, product.toInt, rating.toDouble)
      }
    ).repartition(partitionCount)
  }

  override def setUpBeforeAll(bc: BenchmarkContext): Unit = {
    setUpSparkContext(bc)

    // ALS algorithm parameters.
    alsRankParam = bc.parameter("als_rank").toPositiveInteger
    alsLambdaParam = bc.parameter("als_lambda").toDouble
    alsIterationsParam = bc.parameter("als_iterations").toPositiveInteger

    // Store generated ratings as a single file.
    val ratingsCsv = storeRatings(
      generateRatings(
        bc.parameter("user_count").toPositiveInteger,
        bc.parameter("product_count").toPositiveInteger
      ),
      bc.scratchDirectory().resolve("ratings.csv")
    )

    // Load, partition, and cache the ratings.
    inputRatings = ensureCached(
      loadRatings(ratingsCsv, bc.parameter("spark_executor_count").toPositiveInteger)
    )
  }

  override def run(bc: BenchmarkContext): BenchmarkResult = {
    def trainModel(ratings: RDD[Rating]) = {
      new ALS()
        .setIntermediateRDDStorageLevel(StorageLevel.MEMORY_ONLY)
        .setFinalRDDStorageLevel(StorageLevel.MEMORY_ONLY)
        .setIterations(alsIterationsParam)
        .setLambda(alsLambdaParam)
        .setRank(alsRankParam)
        .setSeed(randomSeed)
        .run(ratings)
    }

    outputMatrixFactorization = trainModel(inputRatings)

    // TODO: add proper validation of the generated model
    Validators.dummy(outputMatrixFactorization)
  }

  override def tearDownAfterAll(bc: BenchmarkContext): Unit = {
    val outputPath = bc.scratchDirectory().resolve("output")
    dumpResult(outputMatrixFactorization, outputPath)

    tearDownSparkContext()
  }

  private def dumpResult(mfm: MatrixFactorizationModel, outputPath: Path): Unit = {
    mfm.userFeatures
      .coalesce(1)
      .map {
        case (user, features) => s"$user: ${features.mkString(", ")}"
      }
      .saveAsTextFile(outputPath.toString)
  }
}
