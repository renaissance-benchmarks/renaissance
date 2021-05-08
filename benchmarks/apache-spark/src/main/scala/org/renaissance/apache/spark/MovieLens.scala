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
import org.renaissance.BenchmarkResult.Validators
import org.renaissance.License
import org.renaissance.apache.spark.ResourceUtil.writeResourceToFile

import java.net.URL
import java.nio.file.Path
import scala.collection.Map
import scala.io.Source
import scala.jdk.CollectionConverters.collectionAsScalaIterableConverter

@Name("movie-lens")
@Group("apache-spark")
@Summary("Recommends movies using the ALS algorithm.")
@Licenses(Array(License.APACHE2))
@Repetitions(20)
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
@Parameter(name = "input_file", defaultValue = "/ratings.csv")
@Parameter(name = "als_ranks", defaultValue = "8, 12")
@Parameter(name = "als_lambdas", defaultValue = "0.1, 10.0")
@Parameter(name = "als_iterations", defaultValue = "10, 20")
@Configuration(
  name = "test",
  settings = Array(
    "input_file = /ratings-small.csv",
    "als_ranks = 12",
    "als_lambdas = 10.0",
    "als_iterations = 10"
  )
)
@Configuration(name = "jmh")
final class MovieLens extends Benchmark with SparkUtil {

  // TODO: Consolidate benchmark parameters across the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/27

  private val randomSeed = 31

  private var inputFileParam: String = _

  private var alsRanksParam: List[Int] = _

  private var alsLambdasParam: List[Double] = _

  private var alsIterationsParam: List[Int] = _

  private val personalRatingsInputFile = "/movie-lens-my-ratings.csv"

  private val moviesInputFile = "/movies.csv"

  private val helper = new MovieLensHelper

  class MovieLensHelper {
    var movies: Map[Int, String] = _
    var ratings: RDD[(Long, Rating)] = _
    var personalRatings: Seq[Rating] = _
    var personalRatingsRDD: RDD[Rating] = _
    var training: RDD[Rating] = _
    var validation: RDD[Rating] = _
    var test: RDD[Rating] = _
    var numTraining: Long = 0
    var numValidation: Long = 0
    var numTest: Long = 0
    var bestModel: Option[MatrixFactorizationModel] = _
    var bestRank = 0
    var bestLambda = -1.0
    var bestNumIter = -1
    var bestValidationRmse = Double.MaxValue
    var numRatings: Long = 0
    var numUsers: Long = 0
    var numMovies: Long = 0

    def loadPersonalRatings(inputFileURL: URL) = {
      val source = Source.fromURL(inputFileURL)

      val personalRatingsIter = source
        .getLines()
        .map { line =>
          val fields = line.split(",")
          Rating(fields(0).toInt, fields(1).toInt, fields(2).toDouble)
        }
        .filter(_.rating > 0.0)

      if (personalRatingsIter.isEmpty) {
        sys.error("No ratings provided.")
      } else {
        personalRatings = personalRatingsIter.toSeq
      }

      personalRatingsRDD = ensureCached(sparkContext.parallelize(personalRatings, 1))
    }

    def loadRatings(file: Path) = {
      ratings = ensureCached(
        createRddFromCsv(
          file,
          header = true,
          delimiter = ",",
          parts => {
            val (user, movie, rating, timestamp) = (parts(0), parts(1), parts(2), parts(3))
            val stratum = timestamp.toLong % 10
            (stratum, Rating(user.toInt, movie.toInt, rating.toDouble))
          }
        )
      )

      numRatings = ratings.count()
      numUsers = ratings.map(_._2.user).distinct().count()
      numMovies = ratings.map(_._2.product).distinct().count()
    }

    def loadMovies(file: Path) = {
      movies = createRddFromCsv(
        file,
        header = true,
        delimiter = ",",
        parts => {
          val (movieId, movieName) = (parts(0), parts(1))
          (movieId.toInt, movieName)
        }
      ).collectAsMap()
    }

    def splitRatings(numPartitions: Int, trainingThreshold: Int, validationThreshold: Int) = {
      training = ensureCached(
        ratings
          .filter(x => x._1 < trainingThreshold)
          .values
          .union(personalRatingsRDD)
          .repartition(numPartitions)
      )
      numTraining = training.count()

      validation = ensureCached(
        ratings
          .filter(x => x._1 >= trainingThreshold && x._1 < validationThreshold)
          .values
          .repartition(numPartitions)
      )
      numValidation = validation.count()

      test = ensureCached(
        ratings
          .filter(x => x._1 >= validationThreshold)
          .values
      )
      numTest = test.count()

      println(
        "Training: " + numTraining + ", validation: " + numValidation + ", test: "
          + numTest
      )
    }

    def trainModels(ranks: List[Int], lambdas: List[Double], iterationCounts: List[Int]) = {

      // Train models and evaluate them on the validation set.

      for (rank <- ranks; lambda <- lambdas; iterations <- iterationCounts) {
        def trainModel(ratings: RDD[Rating]) = {
          new ALS()
            .setIntermediateRDDStorageLevel(StorageLevel.MEMORY_ONLY)
            .setFinalRDDStorageLevel(StorageLevel.MEMORY_ONLY)
            .setIterations(iterations)
            .setLambda(lambda)
            .setRank(rank)
            .setSeed(randomSeed)
            .run(ratings)
        }

        val model = trainModel(training)
        val validationRmse = computeRmse(model, validation, numValidation)
        println(
          "RMSE (validation) = " + validationRmse + " for the model trained with rank = "
            + rank + ", lambda = " + lambda + ", and numIter = " + iterations + "."
        )
        if (validationRmse < bestValidationRmse) {
          bestModel = Some(model)
          bestValidationRmse = validationRmse
          bestRank = rank
          bestLambda = lambda
          bestNumIter = iterations
        }
      }
    }

    def recommendMovies() = {

      val testRmse = computeRmse(bestModel.get, test, numTest)

      println(
        "The best model was trained with rank = " + bestRank + " and lambda = " + bestLambda
          + ", and numIter = " + bestNumIter + ", and its RMSE on the test set is " + testRmse + "."
      )

      // Create a naive baseline and compare it with the best model.

      val meanRating = training.union(validation).map(_.rating).mean
      val baselineRmse =
        math.sqrt(test.map(x => (meanRating - x.rating) * (meanRating - x.rating)).mean)
      val improvement = (baselineRmse - testRmse) / baselineRmse * 100
      println("The best model improves the baseline by " + "%1.2f".format(improvement) + "%.")

      // Make personalized recommendations.

      val myRatedMovieIds = personalRatings.map(_.product).toSet
      val candidates =
        sparkContext.parallelize(movies.keys.filter(!myRatedMovieIds.contains(_)).toSeq)

      val recommendations = bestModel.get
        .predict(candidates.map((0, _)))
        .collect()
        .sortBy(-_.rating)
        .take(50)

      var i = 1
      println("Movies recommended for you:")
      recommendations.foreach { r =>
        println("%2d".format(i) + ": " + movies(r.product))
        i += 1
      }

      recommendations
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
    setUpSparkContext(bc)

    inputFileParam = bc.parameter("input_file").value
    alsRanksParam = bc.parameter("als_ranks").toList(_.toInt).asScala.toList
    alsLambdasParam = bc.parameter("als_lambdas").toList(_.toDouble).asScala.toList
    alsIterationsParam = bc.parameter("als_iterations").toList(_.toInt).asScala.toList

    loadData(bc.scratchDirectory())

    // Split ratings into train (60%), validation (20%), and test (20%) based on the
    // last digit of the timestamp, add myRatings to train, and cache them.
    helper.splitRatings(4, 6, 8)
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
    helper.trainModels(alsRanksParam, alsLambdasParam, alsIterationsParam)
    val recommendations = helper.recommendMovies()

    // TODO: add proper validation
    Validators.dummy(recommendations)
  }

  override def tearDownAfterAll(bc: BenchmarkContext): Unit = {
    tearDownSparkContext()
  }

}
