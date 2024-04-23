package org.renaissance.apache.spark

import org.apache.spark.mllib.recommendation.ALS
import org.apache.spark.mllib.recommendation.MatrixFactorizationModel
import org.apache.spark.mllib.recommendation.Rating
import org.apache.spark.rdd._
import org.apache.spark.storage.StorageLevel
import org.renaissance.Benchmark
import org.renaissance.Benchmark._
import org.renaissance.BenchmarkContext
import org.renaissance.BenchmarkResult
import org.renaissance.BenchmarkResult.Assert
import org.renaissance.BenchmarkResult.ValidationException
import org.renaissance.License
import org.renaissance.apache.spark.ResourceUtil.linesFromUrl
import org.renaissance.apache.spark.ResourceUtil.writeResourceToFile

import java.net.URL
import java.nio.file.Path
import scala.collection.Map

@Name("movie-lens")
@Group("apache-spark")
@Summary("Recommends movies using the ALS algorithm.")
@Licenses(Array(License.APACHE2))
@Repetitions(20)
@Parameter(
  name = "spark_thread_limit",
  defaultValue = "8",
  summary = "Maximum number of threads for the Spark local executor."
)
@Parameter(name = "input_file", defaultValue = "/ratings.csv")
@Parameter(
  name = "als_configs",
  defaultValue =
    "rank,lambda,iterations;" +
      " 8,5.00,20;" +
      "10,2.00,20;" +
      "12,1.00,20;" +
      " 8,0.05,20;" +
      "10,0.01,10;" +
      " 8,0.02,10;" +
      "12,0.10,10;" +
      " 8,0.20,10",
  summary = "A table of ALS configuration parameters to try."
)
@Parameter(
  name = "top_recommended_movie_count",
  defaultValue = "5",
  summary = "Number of top recommended movies to check for expected movies during validation."
)
@Parameter(
  name = "expected_movie_ids",
  defaultValue = "67504,83318,83359,83411,8530",
  summary = "Movie identifiers that must (all) be found among the top recommended movies."
)
@Parameter(
  name = "expected_best_validation_rmse",
  defaultValue = "0.898",
  summary = "The expected RMSE achieved by the best model on the validation subset."
)
@Configuration(
  name = "test",
  settings = Array(
    "input_file = /ratings-small.csv",
    "als_configs = " +
      "rank,lambda,iterations;" +
      "8,0.20,10",
    "top_recommended_movie_count = 2",
    "expected_movie_ids = 1254",
    "expected_best_validation_rmse = 1.086"
  )
)
@Configuration(name = "jmh")
final class MovieLens extends Benchmark with SparkUtil {

  // TODO: Consolidate benchmark parameters across the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/27

  private val randomSeed = 31

  private var inputFileParam: String = _

  private var alsConfigurations: Iterable[AlsConfig] = _

  private val personalRatingsInputFile = "/ratings-personal.csv"

  private val moviesInputFile = "/movies.csv"

  private val helper = new MovieLensHelper

  private var topRecommendedMovieCount: Int = _

  private var expectedMovieIds: Seq[Int] = _

  private var expectedBestValidationRmse: Double = _

  /** Holds ALS training configuration. */
  case class AlsConfig(rank: Int, lambda: Double, iterations: Int)

  class MovieLensHelper {
    var movies: Map[Int, String] = _
    var ratings: RDD[(Long, Rating)] = _
    var personalRatings: Seq[Rating] = _
    var personalRatingsRDD: RDD[Rating] = _
    var personalRatingsUserId: Int = _
    var training: RDD[Rating] = _
    var validation: RDD[Rating] = _
    var test: RDD[Rating] = _
    var numTraining: Long = 0
    var numValidation: Long = 0
    var numTest: Long = 0
    var bestModel: Option[MatrixFactorizationModel] = _
    var bestConfig: AlsConfig = _
    var bestValidationRmse = Double.MaxValue
    var numRatings: Long = 0
    var numUsers: Long = 0
    var numMovies: Long = 0

    private def parseRatingsCsvLines(lines: RDD[String]) = {
      createRddFromCsv(
        lines,
        hasHeader = false,
        delimiter = ",",
        parts => {
          val (userId, movieId, rating, timestamp) = (parts(0), parts(1), parts(2), parts(3))
          val stratum = timestamp.toLong % 10
          (stratum, Rating(userId.toInt, movieId.toInt, rating.toDouble))
        }
      )
    }

    def loadPersonalRatings(url: URL) = {
      // Get only entries with positive rating.
      val lines = sparkContext.parallelize(linesFromUrl(url))
      val ratings = parseRatingsCsvLines(lines).values.filter { _.rating > 0.0 }
      assume(!ratings.isEmpty(), "collection of personal ratings is not empty!")

      val positiveRatings = ratings.collect().toSeq
      val userIds = positiveRatings.map(_.user).distinct
      assume(userIds.length == 1, "personal ratings come from a single user!")

      personalRatings = positiveRatings
      personalRatingsRDD = ensureCached(ratings)
      personalRatingsUserId = userIds.head
    }

    def loadRatings(file: Path) = {
      val lines = sparkContext.textFile(file.toString)
      ratings = ensureCached(parseRatingsCsvLines(lines))

      numRatings = ratings.count()
      numUsers = ratings.map(_._2.user).distinct().count()
      numMovies = ratings.map(_._2.product).distinct().count()
    }

    def loadMovies(file: Path) = {
      movies = createRddFromCsv(
        sparkContext.textFile(file.toString),
        hasHeader = true,
        delimiter = ",",
        parts => {
          val (movieId, movieName) = (parts(0), parts(1))
          (movieId.toInt, movieName)
        }
      ).collectAsMap()
    }

    def splitRatings(trainingThreshold: Int, validationThreshold: Int) = {
      // Merge personal ratings into training data set and cache them.
      training = ensureCached(
        ratings
          .filter(x => x._1 < trainingThreshold)
          .values
          .union(personalRatingsRDD)
      )
      numTraining = training.count()

      validation = ensureCached(
        ratings
          .filter(x => x._1 >= trainingThreshold && x._1 < validationThreshold)
          .values
      )
      numValidation = validation.count()

      test = ensureCached(
        ratings.filter(x => x._1 >= validationThreshold).values
      )
      numTest = test.count()

      println(s"Training: $numTraining, validation: $numValidation, test: $numTest")
    }

    def trainModels(configs: Iterable[AlsConfig]) = {
      // Train models and evaluate them on the validation set.
      for (config <- configs) {
        val model = trainModel(training, config)

        val validationRmse = computeRmse(model, validation, numValidation)
        println(
          s"RMSE (validation) = $validationRmse for the model trained with rank = ${config.rank}, " +
            s"lambda = ${config.lambda}, and numIter = ${config.iterations}."
        )

        if (validationRmse < bestValidationRmse) {
          bestModel = Some(model)
          bestValidationRmse = validationRmse
          bestConfig = config
        }
      }
    }

    private def trainModel(ratings: RDD[Rating], config: AlsConfig) = {
      new ALS()
        .setIntermediateRDDStorageLevel(StorageLevel.MEMORY_ONLY)
        .setFinalRDDStorageLevel(StorageLevel.MEMORY_ONLY)
        .setIterations(config.iterations)
        .setLambda(config.lambda)
        .setRank(config.rank)
        .setSeed(randomSeed)
        .run(ratings)
    }

    def recommendMovies() = {
      val testRmse = computeRmse(bestModel.get, test, numTest)

      println(
        s"The best model was trained with rank = ${bestConfig.rank} and lambda = ${bestConfig.lambda}, " +
          s"and numIter = ${bestConfig.iterations}, and its RMSE on the test set is $testRmse."
      )

      // Create a naive baseline and compare it with the best model.

      val meanRating = training.union(validation).map(_.rating).mean()
      val baselineRmse = math.sqrt(
        test.map(x => (meanRating - x.rating) * (meanRating - x.rating)).mean()
      )

      val improvement = (baselineRmse - testRmse) / baselineRmse * 100
      println(f"The best model improves the baseline by $improvement%.2f%%.")

      // Make personalized recommendations for movies not rated by the user.

      val ratedMovieIds = personalRatings.map(_.product).toSet
      val candidates = sparkContext.parallelize(
        movies.keys.filter(!ratedMovieIds.contains(_)).toSeq.map((personalRatingsUserId, _))
      )

      bestModel.get.predict(candidates).collect()
    }

    /** Compute RMSE (Root Mean Squared Error). */
    def computeRmse(model: MatrixFactorizationModel, data: RDD[Rating], n: Long): Double = {
      val predictions: RDD[Rating] = model.predict(data.map(x => (x.user, x.product)))
      val predictionsAndRatings = predictions
        .map(x => ((x.user, x.product), x.rating))
        .join(data.map(x => ((x.user, x.product), x.rating)))
        .values
      math.sqrt(predictionsAndRatings.map(x => (x._1 - x._2) * (x._1 - x._2)).reduce(_ + _) / n)
    }
  }

  override def setUpBeforeAll(bc: BenchmarkContext): Unit = {
    import scala.jdk.CollectionConverters._

    // Validation parameters.
    topRecommendedMovieCount = bc.parameter("top_recommended_movie_count").toInteger
    expectedMovieIds = bc.parameter("expected_movie_ids").toList(_.toInt).asScala.toSeq
    expectedBestValidationRmse = bc.parameter("expected_best_validation_rmse").toDouble

    //
    // Without a checkpoint directory set, JMH runs of this
    // benchmark in Travis CI tend to crash with stack overflow.
    //
    // TODO Only use checkpoint directory in test runs.
    //
    setUpSparkContext(bc, useCheckpointDir = true)

    inputFileParam = bc.parameter("input_file").value

    alsConfigurations = bc
      .parameter("als_configs")
      .toCsvRows(m =>
        AlsConfig(
          m.get("rank").toInt,
          m.get("lambda").toDouble,
          m.get("iterations").toInt
        )
      )
      .asScala

    loadData(bc.scratchDirectory())

    // Split ratings into training (~60%), validation (~20%), and test (~20%)
    // data sets based on the last digit of a rating's timestamp.
    helper.splitRatings(6, 8)
  }

  def loadData(scratchDir: Path) = {
    helper.loadPersonalRatings(getClass.getResource(personalRatingsInputFile))
    helper.loadRatings(writeResourceToFile(inputFileParam, scratchDir.resolve("ratings.csv")))
    helper.loadMovies(writeResourceToFile(moviesInputFile, scratchDir.resolve("movies.csv")))

    println(
      "Got " + helper.numRatings + " ratings from "
        + helper.numUsers + " users on " + helper.numMovies + " movies."
    )
  }

  override def run(bc: BenchmarkContext): BenchmarkResult = {
    helper.trainModels(alsConfigurations)

    val topRecommended = helper
      .recommendMovies()
      .sortBy(r => (-r.rating, r.product))
      .take(topRecommendedMovieCount)

    println(s"Top recommended movies for user id ${helper.personalRatingsUserId}:")
    topRecommended.zipWithIndex.foreach {
      case (r: Rating, i: Int) =>
        println(
          f"${i + 1}%2d: ${helper.movies(r.product)}%s (rating: ${r.rating}%.3f, id: ${r.product}%d)"
        )
    }

    () => validate(topRecommended)
  }

  private def validate(recommendedMovies: Array[Rating]): Unit = {
    val recommendedMovieIds = recommendedMovies.map(_.product)
    expectedMovieIds.foreach(expectedId => {
      if (!recommendedMovieIds.contains(expectedId)) {
        throw new ValidationException(
          s"Expected ${recommendedMovies.length} top-rated movies to contain movie with id $expectedId"
        )
      }
    })

    Assert.assertEquals(
      expectedBestValidationRmse,
      helper.bestValidationRmse,
      0.005,
      "Best model RMSE on the validation set"
    )
  }

  override def tearDownAfterAll(bc: BenchmarkContext): Unit = {
    tearDownSparkContext()
  }

}
