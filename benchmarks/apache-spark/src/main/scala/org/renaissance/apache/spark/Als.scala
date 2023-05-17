package org.renaissance.apache.spark

import org.apache.spark.ml.recommendation.ALS
import org.apache.spark.ml.recommendation.ALS.Rating
import org.apache.spark.ml.recommendation.ALSModel
import org.apache.spark.sql.DataFrame
import org.renaissance.Benchmark
import org.renaissance.Benchmark._
import org.renaissance.BenchmarkContext
import org.renaissance.BenchmarkResult
import org.renaissance.BenchmarkResult.Validators
import org.renaissance.License

import java.nio.file.Files
import java.nio.file.Path
import scala.util.Random

@Name("als")
@Group("apache-spark")
@Summary("Runs the ALS algorithm from the Spark ML library.")
@Licenses(Array(License.APACHE2))
@SupportsJvm("20")
@Repetitions(30)
@Parameter(
  name = "spark_thread_limit",
  defaultValue = "12",
  summary = "Maximum number of threads for the Spark local executor."
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

  private var inputRatings: DataFrame = _

  private var outputAlsModel: ALSModel = _

  private type Rating = ALS.Rating[Int]

  private def generateRatings(userCount: Int, productCount: Int): Seq[Rating] = {
    // TODO: Use a Renaissance-provided random generator.
    val rand = new Random(randomSeed)

    for (userId <- 0 until userCount; itemId <- 0 until productCount) yield {
      val rating = 1 + rand.nextInt(3) + rand.nextInt(3)
      Rating[Int](userId, itemId, rating.toFloat)
    }
  }

  private def storeRatings(ratings: Seq[Rating], file: Path): Path = {
    import scala.jdk.CollectionConverters._

    val header = Seq(Seq("user", "item", "rating").mkString(","))
    val lines = header ++ ratings.map(r => Rating.unapply(r).get.productIterator.mkString(","))
    Files.write(file, lines.asJava)
  }

  private def loadRatings(file: Path) = {
    sparkSession.read
      .option("header", true)
      .schema("user INT, item INT, rating FLOAT")
      .csv(file.toString)
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
    inputRatings = ensureCached(loadRatings(ratingsCsv))
  }

  override def run(bc: BenchmarkContext): BenchmarkResult = {
    def trainModel(ratings: DataFrame) = {
      new ALS()
        .setIntermediateStorageLevel("MEMORY_ONLY")
        .setFinalStorageLevel("MEMORY_ONLY")
        .setMaxIter(alsIterationsParam)
        .setRegParam(alsLambdaParam)
        .setRank(alsRankParam)
        .setSeed(randomSeed)
        .fit(ratings)
    }

    outputAlsModel = trainModel(inputRatings)

    // TODO: add proper validation of the generated model
    Validators.dummy(outputAlsModel)
  }

  override def tearDownAfterAll(bc: BenchmarkContext): Unit = {
    if (dumpResultsBeforeTearDown && outputAlsModel != null) {
      val outputPath = bc.scratchDirectory().resolve("output")
      dumpResult(outputAlsModel, outputPath)
    }

    tearDownSparkContext()
  }

  private def dumpResult(am: ALSModel, outputPath: Path): Unit = {
    val outputFile = outputPath.resolve("users").toString
    am.userFactors.coalesce(1).write.json(outputFile)
  }
}
