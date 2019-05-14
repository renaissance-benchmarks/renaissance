package org.renaissance.apache.spark

import java.io.InputStream
import java.net.URL
import java.nio.charset.StandardCharsets
import java.nio.file.Path
import java.nio.file.Paths

import org.apache.commons.io.FileUtils
import org.apache.commons.io.IOUtils
import org.apache.log4j.Level
import org.apache.log4j.Logger
import org.apache.spark.SparkContext
import org.apache.spark.mllib.recommendation.ALS
import org.apache.spark.mllib.recommendation.MatrixFactorizationModel
import org.apache.spark.mllib.recommendation.Rating
import org.apache.spark.rdd._
import org.renaissance.Config
import org.renaissance.License
import org.renaissance.RenaissanceBenchmark
import org.renaissance.Benchmark._

import scala.io.Source

@Name("movie-lens")
@Group("apache-spark")
@Summary("Recommends movies using the ALS algorithm.")
@Licenses(Array(License.APACHE2))
@Repetitions(20)
class MovieLens extends RenaissanceBenchmark with SparkUtil {

  // TODO: Consolidate benchmark parameters across the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/27

  val THREAD_COUNT = Runtime.getRuntime.availableProcessors

  // TODO: Unify handling of scratch directories throughout the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/13

  var sc: SparkContext = null

  val movieLensPath = Paths.get("target", "movie-lens")

  val checkpointPath = movieLensPath.resolve("checkpoint")

  val personalRatingsInputFile = "/movie-lens-my-ratings.csv"

  val moviesInputFile = "/movies.csv"

  var ratingsInputFile = "/ratings.csv"

  val ratingsSmallInputFile = "/ratings-small.csv"

  val bigFilesPath = movieLensPath.resolve("bigfiles")

  val moviesBigFile = bigFilesPath.resolve("movies.txt")

  val ratingsBigFile = bigFilesPath.resolve("ratings.txt")

  var tempDirPath: Path = null

  var alsRanks = List(8, 12)

  var alsLambdas = List(0.1, 10.0)

  var alsNumIters = List(10, 20)

  class MovieLensHelper {
    var movies: Map[Int, String] = null
    var ratings: RDD[(Long, Rating)] = null
    var personalRatings: Seq[Rating] = null
    var personalRatingsRDD: RDD[Rating] = null
    var training: RDD[Rating] = null
    var validation: RDD[Rating] = null
    var test: RDD[Rating] = null
    var numTraining: Long = 0
    var numValidation: Long = 0
    var numTest: Long = 0
    var bestModel: Option[MatrixFactorizationModel] = null
    var bestRank = 0
    var bestLambda = -1.0
    var bestNumIter = -1
    var bestValidationRmse = Double.MaxValue
    var numRatings: Long = 0
    var numUsers: Long = 0
    var numMovies: Long = 0

    def loadPersonalRatings(inputFileURL: URL) = {
      val lines = Source.fromURL(inputFileURL).getLines()

      val personalRatingsIter = lines
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

      personalRatingsRDD = sc.parallelize(personalRatings, 1)
    }

    def getFilteredRDDFromPath(inputPath: Path): RDD[String] = {
      val rdd = sc.textFile(inputPath.toString)
      val header = rdd.first
      return rdd
        .filter { line =>
          line != header
        }
    }

    def loadRatings(inputPath: Path) = {

      ratings = getFilteredRDDFromPath(inputPath)
        .map { line =>
          val fields = line.split(",")
          // Format: (timestamp % 10, Rating(userId, movieId, rating))
          (fields(3).toLong % 10, Rating(fields(0).toInt, fields(1).toInt, fields(2).toDouble))
        }

      numRatings = ratings.count()
      numUsers = ratings.map(_._2.user).distinct().count()
      numMovies = ratings.map(_._2.product).distinct().count()

    }

    def loadMovies(inputPath: Path) = {

      movies = getFilteredRDDFromPath(inputPath)
        .map { line =>
          val fields = line.split(",")
          // Format: (movieId, movieName)
          (fields(0).toInt, fields(1))
        }
        .collect()
        .toMap
    }

    def splitRatings(numPartitions: Int, trainingThreshold: Int, validationThreshold: Int) = {

      training = ratings
        .filter(x => x._1 < trainingThreshold)
        .values
        .union(personalRatingsRDD)
        .repartition(numPartitions)
        .cache()
      numTraining = training.count()

      validation = ratings
        .filter(x => x._1 >= trainingThreshold && x._1 < validationThreshold)
        .values
        .repartition(numPartitions)
        .cache()
      numValidation = validation.count()

      test = ratings
        .filter(x => x._1 >= validationThreshold)
        .values
        .cache()
      numTest = test.count()

      println(
        "Training: " + numTraining + ", validation: " + numValidation + ", test: "
          + numTest
      )
    }

    def trainModels(ranks: List[Int], lambdas: List[Double], numIters: List[Int]) = {

      // Train models and evaluate them on the validation set.

      for (rank <- ranks; lambda <- lambdas; numIter <- numIters) {
        val model = ALS.train(training, rank, numIter, lambda)
        val validationRmse = computeRmse(model, validation, numValidation)
        println(
          "RMSE (validation) = " + validationRmse + " for the model trained with rank = "
            + rank + ", lambda = " + lambda + ", and numIter = " + numIter + "."
        )
        if (validationRmse < bestValidationRmse) {
          bestModel = Some(model)
          bestValidationRmse = validationRmse
          bestRank = rank
          bestLambda = lambda
          bestNumIter = numIter
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
      val candidates = sc.parallelize(movies.keys.filter(!myRatedMovieIds.contains(_)).toSeq)

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

  def setUpLogger() = {
    Logger.getLogger("org.apache.spark").setLevel(Level.ERROR)
    Logger.getLogger("org.eclipse.jetty.server").setLevel(Level.OFF)
  }

  override def setUpBeforeAll(c: Config): Unit = {
    tempDirPath = RenaissanceBenchmark.generateTempDir("movie_lens")
    setUpLogger()
    sc = setUpSparkContext(tempDirPath, THREAD_COUNT)
    sc.setCheckpointDir(checkpointPath.toString)
    if (c.functionalTest) {
      ratingsInputFile = ratingsSmallInputFile
      alsRanks = List(12)
      alsLambdas = List(10.0)
      alsNumIters = List(10)
    }
  }

  def writeResourceToFile(resourceStream: InputStream, outputPath: Path) = {
    val content = IOUtils.toString(resourceStream, StandardCharsets.UTF_8)
    FileUtils.write(outputPath.toFile, content, StandardCharsets.UTF_8, true)
  }

  def loadData(helper: MovieLensHelper) = {
    FileUtils.deleteDirectory(bigFilesPath.toFile)

    helper.loadPersonalRatings(this.getClass.getResource(personalRatingsInputFile))

    writeResourceToFile(this.getClass.getResourceAsStream(ratingsInputFile), ratingsBigFile)
    helper.loadRatings(ratingsBigFile)

    writeResourceToFile(this.getClass.getResourceAsStream(moviesInputFile), moviesBigFile)
    helper.loadMovies(moviesBigFile)

    println(
      "Got " + helper.numRatings + " ratings from "
        + helper.numUsers + " users on " + helper.numMovies + " movies."
    )
  }

  override def runIteration(c: Config): Unit = {
    var helper = new MovieLensHelper
    loadData(helper)

    // Split ratings into train (60%), validation (20%), and test (20%) based on the
    // last digit of the timestamp, add myRatings to train, and cache them.
    helper.splitRatings(4, 6, 8)

    helper.trainModels(alsRanks, alsLambdas, alsNumIters)
    helper.recommendMovies()
  }

  override def tearDownAfterAll(c: Config): Unit = {
    tearDownSparkContext(sc)
    RenaissanceBenchmark.deleteTempDir(tempDirPath)
  }

}
