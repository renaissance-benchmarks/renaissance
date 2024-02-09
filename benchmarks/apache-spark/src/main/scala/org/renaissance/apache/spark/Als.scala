package org.renaissance.apache.spark

import org.apache.spark.ml.recommendation.ALS
import org.apache.spark.ml.recommendation.ALS.Rating
import org.apache.spark.ml.recommendation.ALSModel
import org.apache.spark.sql.DataFrame
import org.renaissance.Benchmark
import org.renaissance.Benchmark._
import org.renaissance.BenchmarkContext
import org.renaissance.BenchmarkResult
import org.renaissance.BenchmarkResult.Assert
import org.renaissance.License

import java.nio.file.Files
import java.nio.file.Path
import scala.util.Random

@Name("als")
@Group("apache-spark")
@Summary("Runs the ALS algorithm from the Spark ML library.")
@Licenses(Array(License.APACHE2))
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
  name = "item_count",
  defaultValue = "100",
  summary = "Number of items rated by each user."
)
@Parameter(name = "als_rank", defaultValue = "10")
@Parameter(name = "als_lambda", defaultValue = "0.01")
@Parameter(name = "als_iterations", defaultValue = "10")
@Parameter(name = "expected_user_factors_sum", defaultValue = "-9596.627819650528")
@Parameter(name = "expected_user_factors_sum_squares", defaultValue = "788656.1993662444")
@Parameter(name = "expected_item_factors_sum", defaultValue = "-3.6123005696281325")
@Parameter(name = "expected_item_factors_sum_squares", defaultValue = "121.76721351321395")
@Configuration(
  name = "test",
  settings = Array(
    "user_count = 500",
    "expected_user_factors_sum = -599.6017655955875",
    "expected_user_factors_sum_squares = 5474.245809443889",
    "expected_item_factors_sum = -32.74099353258498",
    "expected_item_factors_sum_squares = 212.4680732798157"
  )
)
@Configuration(name = "jmh")
final class Als extends Benchmark with SparkUtil {

  // Utility classes for validation.

  private case class ClosedInterval(start: Int, end: Int) {

    def expand(other: ClosedInterval): ClosedInterval = {
      ClosedInterval(start.min(other.start), end.max(other.end))
    }
  }

  private object ClosedInterval {
    def apply(value: Int): ClosedInterval = ClosedInterval(value, value)
  }

  private case class FactorsSummary(
    sum: Double,
    sumSquares: Double,
    matrixWidthInterval: ClosedInterval,
    matrixHeight: Int
  )

  // TODO: Consolidate benchmark parameters across the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/27

  private val randomSeed = 17

  private var alsRankParam: Int = _

  private var alsLambdaParam: Double = _

  private var alsIterationsParam: Int = _

  private var alsUserCount: Int = _

  private var alsItemCount: Int = _

  private var expectedUserFactorsSummary: FactorsSummary = _

  private var expectedItemFactorsSummary: FactorsSummary = _

  private var inputRatings: DataFrame = _

  private type Rating = ALS.Rating[Int]

  private def generateRatings(userCount: Int, itemCount: Int): Seq[Rating] = {
    // TODO: Use a Renaissance-provided random generator.
    val rand = new Random(randomSeed)

    for (userId <- 0 until userCount; itemId <- 0 until itemCount) yield {
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
      .option("header", value = true)
      .schema("user INT, item INT, rating FLOAT")
      .csv(file.toString)
  }

  override def setUpBeforeAll(bc: BenchmarkContext): Unit = {
    setUpSparkContext(bc)

    // ALS algorithm parameters.
    alsRankParam = bc.parameter("als_rank").toPositiveInteger
    alsLambdaParam = bc.parameter("als_lambda").toDouble
    alsIterationsParam = bc.parameter("als_iterations").toPositiveInteger
    alsUserCount = bc.parameter("user_count").toPositiveInteger
    alsItemCount = bc.parameter("item_count").toPositiveInteger

    // Validation parameters.
    expectedUserFactorsSummary = FactorsSummary(
      bc.parameter("expected_user_factors_sum").toDouble,
      bc.parameter("expected_user_factors_sum_squares").toDouble,
      ClosedInterval(alsRankParam),
      alsUserCount
    )

    expectedItemFactorsSummary = FactorsSummary(
      bc.parameter("expected_item_factors_sum").toDouble,
      bc.parameter("expected_item_factors_sum_squares").toDouble,
      ClosedInterval(alsRankParam),
      alsItemCount
    )

    // Store generated ratings as a single file.
    val ratingsCsv = storeRatings(
      generateRatings(alsUserCount, alsItemCount),
      bc.scratchDirectory().resolve("ratings.csv")
    )

    // Load, partition, and cache the ratings.
    inputRatings = ensureCached(loadRatings(ratingsCsv))
  }

  override def run(bc: BenchmarkContext): BenchmarkResult = {
    val als = new ALS()
      .setIntermediateStorageLevel("MEMORY_ONLY")
      .setFinalStorageLevel("MEMORY_ONLY")
      .setMaxIter(alsIterationsParam)
      .setRegParam(alsLambdaParam)
      .setRank(alsRankParam)
      .setSeed(randomSeed)

    val alsModel = als.fit(inputRatings)
    () => validate(alsModel)
  }

  private def validate(result: ALSModel): Unit = {
    val actualUserFactorsSummary = summarizeFactors(result.userFactors)
    validateSummary("user", expectedUserFactorsSummary, actualUserFactorsSummary, 0.01)

    val actualItemFactorsSummary = summarizeFactors(result.itemFactors)
    validateSummary("item", expectedItemFactorsSummary, actualItemFactorsSummary, 0.000001)
  }

  private def summarizeFactors(factors: DataFrame): FactorsSummary = {
    import scala.collection.mutable

    val collectedFactors = factors
      .collect()
      .map(row => row.getAs("features").asInstanceOf[mutable.Seq[Float]].map(_.toDouble))

    val flatFactors = collectedFactors.flatten

    val matrixWidthRange: ClosedInterval = collectedFactors
      .map(row => ClosedInterval(row.length))
      .reduce((range1, range2) => range1.expand(range2))

    FactorsSummary(
      flatFactors.sum,
      flatFactors.map(v => v * v).sum,
      matrixWidthRange,
      collectedFactors.length
    )
  }

  private def validateSummary(
    kind: String,
    expected: FactorsSummary,
    actual: FactorsSummary,
    tolerance: Double
  ): Unit = {
    // Validate factors matrix content.
    Assert.assertEquals(expected.sum, actual.sum, tolerance, s"sum of $kind factors")

    Assert.assertEquals(
      expected.sumSquares,
      actual.sumSquares,
      tolerance,
      s"sum of squares of $kind factors"
    )

    // Validate factors matrix shape.
    Assert.assertEquals(
      expected.matrixWidthInterval.start,
      actual.matrixWidthInterval.start,
      s"$kind features matrix width"
    )

    Assert.assertEquals(
      expected.matrixWidthInterval.end,
      actual.matrixWidthInterval.end,
      s"$kind features matrix width"
    )

    Assert.assertEquals(
      expected.matrixHeight,
      actual.matrixHeight,
      s"$kind features matrix height"
    )
  }

  override def tearDownAfterAll(bc: BenchmarkContext): Unit = {
    tearDownSparkContext()
  }
}
