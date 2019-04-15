package org.renaissance.apache.spark

import java.io.File
import java.io.InputStream
import java.net.URL
import java.nio.charset.StandardCharsets
import java.nio.file.{Path, Paths}

import scala.io.Source
import org.apache.commons.io.FileUtils
import org.apache.commons.io.IOUtils
import org.apache.log4j.Logger
import org.apache.log4j.Level
import org.apache.spark.SparkConf
import org.apache.spark.SparkContext
import org.apache.spark.SparkContext._
import org.apache.spark.rdd._
import org.apache.spark.mllib.recommendation.{ALS, MatrixFactorizationModel, Rating}
import org.renaissance.Config
import org.renaissance.License
import org.renaissance.RenaissanceBenchmark

class MovieLens extends RenaissanceBenchmark {

  def description = "Recommends movies using the ALS algorithm."

  override def defaultRepetitions = 5

  override def licenses = License.create(License.APACHE2)

  val THREAD_COUNT = Runtime.getRuntime.availableProcessors

  var sc: SparkContext = null

  val movieLensPath = Paths.get("target", "movie-lens")

  val checkpointPath = movieLensPath.resolve("checkpoint")

  val myRatingsInputFile = File.separator + "movie-lens-my-ratings.csv"

  val moviesInputFile = File.separator +"movies.csv"

  val ratingsInputFile = File.separator +"ratings.csv"

  val bigFilesPath = movieLensPath.resolve("bigfiles")

  val moviesBigFile = bigFilesPath.resolve("movies.txt")

  val ratingsBigFile = bigFilesPath.resolve("ratings.txt")

  var tempDirPath: Path = null

  def setUpLogger() = {
    Logger.getLogger("org.apache.spark").setLevel(Level.ERROR)
    Logger.getLogger("org.eclipse.jetty.server").setLevel(Level.OFF)
  }

  def setUpSpark() = {
    val conf = new SparkConf()
      .setAppName("movie-lens")
      .setMaster(s"local[$THREAD_COUNT]")
      .set("spark.local.dir", tempDirPath.toString)
    sc = new SparkContext(conf)
    sc.setCheckpointDir(checkpointPath.toString)
  }

  override def setUpBeforeAll(c: Config): Unit = {
    tempDirPath = RenaissanceBenchmark.generateTempDir("movie_lens")
    setUpLogger()
    setUpSpark()
  }

  override def runIteration(c: Config): Unit = {
    run(sc)
  }

  override def tearDownAfterAll(c: Config): Unit = {
    sc.stop()
    RenaissanceBenchmark.deleteTempDir(tempDirPath)
  }

  def run(sc: SparkContext): Unit = {

    // Load personal ratings.
    val myRatings = loadRatings(this.getClass.getResource(myRatingsInputFile))
    val myRatingsRDD = sc.parallelize(myRatings, 1)

    // Load ratings and movie titles.

    FileUtils.deleteDirectory(bigFilesPath.toFile)

    val ratingsText = IOUtils.toString(
      this.getClass.getResourceAsStream(ratingsInputFile),
      StandardCharsets.UTF_8
    )
    FileUtils.write(ratingsBigFile.toFile, ratingsText, StandardCharsets.UTF_8, true)
    val ratingsFile = sc.textFile(ratingsBigFile.toString)
    val ratingsFileHeader = ratingsFile.first
    val ratings = ratingsFile
      .filter { line =>
        line != ratingsFileHeader
      }
      .map { line =>
        val fields = line.split(",")
        // Format: (timestamp % 10, Rating(userId, movieId, rating))
        (fields(3).toLong % 10, Rating(fields(0).toInt, fields(1).toInt, fields(2).toDouble))
      }

    val moviesText = IOUtils.toString(
      this.getClass.getResourceAsStream(moviesInputFile),
      StandardCharsets.UTF_8
    )
    FileUtils.write(moviesBigFile.toFile, moviesText, StandardCharsets.UTF_8, true)
    val moviesFile = sc.textFile(moviesBigFile.toString)
    val moviesFileHeader = moviesFile.first
    val movies = moviesFile
      .filter { line =>
        line != moviesFileHeader
      }
      .map { line =>
        val fields = line.split(",")
        // Format: (movieId, movieName)
        (fields(0).toInt, fields(1))
      }
      .collect()
      .toMap

    val numRatings = ratings.count()
    val numUsers = ratings.map(_._2.user).distinct().count()
    val numMovies = ratings.map(_._2.product).distinct().count()

    println(
      "Got " + numRatings + " ratings from "
        + numUsers + " users on " + numMovies + " movies."
    )

    // Split ratings into train (60%), validation (20%), and test (20%) based on the
    // last digit of the timestamp, add myRatings to train, and cache them.

    val numPartitions = 4
    val training = ratings
      .filter(x => x._1 < 6)
      .values
      .union(myRatingsRDD)
      .repartition(numPartitions)
      .cache()
    val validation = ratings
      .filter(x => x._1 >= 6 && x._1 < 8)
      .values
      .repartition(numPartitions)
      .cache()
    val test = ratings.filter(x => x._1 >= 8).values.cache()

    val numTraining = training.count()
    val numValidation = validation.count()
    val numTest = test.count()

    println(
      "Training: " + numTraining + ", validation: " + numValidation + ", test: " + numTest
    )

    // Train models and evaluate them on the validation set.

    val ranks = List(8, 12)
    val lambdas = List(0.1, 10.0)
    val numIters = List(10, 20)
    var bestModel: Option[MatrixFactorizationModel] = None
    var bestValidationRmse = Double.MaxValue
    var bestRank = 0
    var bestLambda = -1.0
    var bestNumIter = -1
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

    // Evaluate the best model on the test set.

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

    val myRatedMovieIds = myRatings.map(_.product).toSet
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

  /** Load ratings from file. */
  def loadRatings(path: URL): Seq[Rating] = {
    //val lines = Source.fromURL(path, StandardCharsets.UTF_8).getLines()
    val lines = Source.fromURL(path).getLines()
    //System.out.println(path)
    //val lines = Source.fromInputStream(path).getLines()
    //val lines = Source.fromFile(path).getLines()

    val ratings = lines
      .map { line =>
        val fields = line.split(",")
        Rating(fields(0).toInt, fields(1).toInt, fields(2).toDouble)
      }
      .filter(_.rating > 0.0)
    if (ratings.isEmpty) {
      sys.error("No ratings provided.")
    } else {
      ratings.toSeq
    }
  }
}
