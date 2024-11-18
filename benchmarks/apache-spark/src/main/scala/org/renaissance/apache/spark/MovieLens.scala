package org.renaissance.apache.spark

import org.apache.spark.mllib.recommendation.ALS
import org.apache.spark.mllib.recommendation.MatrixFactorizationModel
import org.apache.spark.mllib.recommendation.Rating
import org.apache.spark.rdd.RDD
import org.apache.spark.sql.types._
import org.apache.spark.sql.DataFrame
import org.apache.spark.sql.Encoder
import org.apache.spark.sql.Encoders
import org.apache.spark.storage.StorageLevel
import org.renaissance.Benchmark
import org.renaissance.Benchmark._
import org.renaissance.BenchmarkContext
import org.renaissance.BenchmarkResult
import org.renaissance.BenchmarkResult.Assert
import org.renaissance.BenchmarkResult.ValidationException
import org.renaissance.License
import org.renaissance.apache.spark.ResourceUtil.linesFromSource
import org.renaissance.apache.spark.ResourceUtil.sourceFromResource

import java.net.URL
import java.nio.file.Path
import scala.collection.Map
import scala.io.Source

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
    var personalRatings: Seq[Rating] = _
    var personalRatingsUserId: Int = _
    var training: RDD[Rating] = _
    var validation: RDD[Rating] = _
    var test: RDD[Rating] = _
    var numValidation: Long = 0
    var numTest: Long = 0
    var bestModel: Option[MatrixFactorizationModel] = _
    var bestConfig: AlsConfig = _
    var bestValidationRmse = Double.MaxValue

    private def dataFrameFromCsvLines(
      lines: Seq[String],
      schema: StructType,
      hasHeader: Boolean
    ): DataFrame = {
      implicit val encoder: Encoder[String] = Encoders.STRING
      val ds = sparkSession.createDataset(lines)
      val reader = sparkSession.read.option("header", value = hasHeader).schema(schema)

      // Repartition the dataset to mimic the default used by textfile().
      reader.csv(ds).repartition(sparkContext.defaultMinPartitions)
    }

    private def ratingsRddFromCsvLines(lines: Seq[String]) = {
      val schema = StructType(
        Seq(
          StructField("userId", IntegerType, false),
          StructField("movieId", IntegerType, false),
          StructField("rating", DoubleType, false),
          StructField("timestamp", LongType, false)
        )
      )

      dataFrameFromCsvLines(lines, schema, hasHeader = false).rdd.map { row =>
        val stratum = row.getAs[Long]("timestamp") % 10
        val rating = Rating(row.getAs("userId"), row.getAs("movieId"), row.getAs("rating"))
        (stratum, rating)
      }
    }

    private def moviesRddFromCsvLines(lines: Seq[String]) = {
      val schema = StructType(
        Seq(
          StructField("movieId", IntegerType, false),
          StructField("title", StringType, false),
          StructField("genres", StringType, false)
        )
      )

      dataFrameFromCsvLines(lines, schema, hasHeader = true).rdd.map { row =>
        (row.getAs[Int]("movieId"), row.getAs[String]("title"))
      }
    }

    private def initMovies(source: Source): Unit = {
      movies = moviesRddFromCsvLines(linesFromSource(source)).collect().toMap
    }

    def loadData(
      moviesSource: Source,
      personalRatingsSource: Source,
      ratingsSource: Source,
      trainingThreshold: Int,
      validationThreshold: Int
    ): Unit = {
      initMovies(moviesSource)

      val personalRatingsRdd = initPersonalRatings(loadPersonalRatings(personalRatingsSource))
      val ratingsRdd = describeRatings(ratingsRddFromCsvLines(linesFromSource(ratingsSource)))
      val parts = splitRatings(ratingsRdd, trainingThreshold, validationThreshold)

      // Merge personal ratings into training data set.
      initDatasets(parts._1.union(personalRatingsRdd), parts._2, parts._3)
    }

    private def loadPersonalRatings(source: Source) = {
      // Get only entries with positive rating.
      ratingsRddFromCsvLines(linesFromSource(source)).values.filter { _.rating > 0.0 }
    }

    private def initPersonalRatings(ratings: RDD[Rating]) = {
      assume(!ratings.isEmpty(), "collection of personal ratings is not empty!")

      val collectedRatings = ratings.collect().toSeq
      val userIds = collectedRatings.map(_.user).distinct
      assume(userIds.length == 1, "personal ratings come from a single user!")

      personalRatings = collectedRatings
      personalRatingsUserId = userIds.head

      ratings
    }

    private def describeRatings(ratings: RDD[(Long, Rating)]) = {
      val numRatings = ratings.count()
      val numUsers = ratings.map(_._2.user).distinct().count()
      val numMovies = ratings.map(_._2.product).distinct().count()
      println(s"Got $numRatings ratings from $numUsers users on $numMovies movies.")
      ratings
    }

    private def splitRatings(
      ratings: RDD[(Long, Rating)],
      trainingThreshold: Int,
      validationThreshold: Int
    ) = {
      (
        ratings.filter(x => x._1 < trainingThreshold).values,
        ratings.filter(x => x._1 >= trainingThreshold && x._1 < validationThreshold).values,
        ratings.filter(x => x._1 >= validationThreshold).values
      )
    }

    private def initDatasets(
      trainingSet: RDD[Rating],
      validationSet: RDD[Rating],
      testSet: RDD[Rating]
    ): Unit = {
      // Cache data sets and print info to trigger evaluation.
      training = ensureCached(trainingSet)

      validation = ensureCached(validationSet)
      numValidation = validation.count()

      test = ensureCached(testSet)
      numTest = test.count()

      println(s"Training: ${training.count()}, validation: $numValidation, test: $numTest")
    }

    def trainModels(configs: Iterable[AlsConfig]): Unit = {
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

    def recommendMovies(): Array[Rating] = {
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
    import scala.jdk.CollectionConverters.ListHasAsScala

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

    // Load movies and ratings and split the ratings into training (~60%),
    // validation (~20%), and test (~20%) sets based on the last digit of a
    // rating's timestamp.
    val ratingsInputFileParam = bc.parameter("input_file").value

    helper.loadData(
      sourceFromResource(moviesInputFile),
      sourceFromResource(personalRatingsInputFile),
      sourceFromResource(ratingsInputFileParam),
      6,
      8
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
