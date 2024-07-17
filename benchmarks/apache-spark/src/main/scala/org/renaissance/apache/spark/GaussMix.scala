package org.renaissance.apache.spark

import org.apache.spark.mllib.clustering.GaussianMixture
import org.apache.spark.mllib.clustering.GaussianMixtureModel
import org.apache.spark.mllib.linalg.Vectors
import org.apache.spark.rdd.RDD
import org.renaissance.Benchmark
import org.renaissance.Benchmark._
import org.renaissance.BenchmarkContext
import org.renaissance.BenchmarkResult
import org.renaissance.BenchmarkResult.ValidationException
import org.renaissance.License

import scala.util.Random

@Name("gauss-mix")
@Group("apache-spark")
@Summary("Computes a Gaussian mixture model using expectation-maximization.")
@Licenses(Array(License.APACHE2))
@Repetitions(40)
@Parameter(
  name = "spark_thread_limit",
  defaultValue = "4",
  summary = "Maximum number of threads for the Spark local executor."
)
@Parameter(
  name = "point_count",
  defaultValue = "9000",
  summary = "Number of data points to generate."
)
@Parameter(
  name = "dimension_count",
  defaultValue = "8",
  summary = "Number of dimensions in each data point."
)
@Parameter(
  name = "cluster_count",
  defaultValue = "6",
  summary = "Number of point clusters to generate."
)
@Parameter(
  name = "cluster_distance",
  defaultValue = "5",
  summary = "Distance (in a single dimension) between generated gaussian clusters."
)
@Parameter(
  name = "gm_configs",
  defaultValue =
    "model_count,gaussians_per_cluster,iteration_count;" +
      "4,2.0,25;" +
      "4,1.5,30;"
)
@Parameter(
  name = "prediction_tolerance",
  defaultValue = "0.25",
  summary = "Tolerance between assigned and expected gaussian mu value of points."
)
@Parameter(
  name = "expected_model_accuracy",
  defaultValue = "0.99",
  summary = "Expected percentage of points correctly assigned to centroids."
)
@Configuration(
  name = "test",
  settings = Array(
    "point_count = 2500",
    "cluster_count = 2",
    "gm_configs = " +
      "model_count,gaussians_per_cluster,iteration_count;" +
      "2,2.0,25;"
  )
)
@Configuration(name = "jmh")
final class GaussMix extends Benchmark with SparkUtil {

  // TODO: Consolidate benchmark parameters across the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/27

  private var predictionTolerance: Double = _

  private var expectedModelAccuracy: Double = _

  private type Point = org.apache.spark.mllib.linalg.Vector

  private var trainingPoints: RDD[Point] = _

  private var validationPoints: RDD[Point] = _

  private var validationCentroids: RDD[Point] = _

  private var testingPoints: RDD[Point] = _

  private var testingCentroids: RDD[Point] = _

  private case class GmConfig(
    /** The number of models (with different random seed) to train. */
    modelCount: Int,
    /** The number of gaussians to use in the model. */
    gaussianCount: Int,
    /** The maximum number of iterations for training the model. */
    iterationCount: Int
  )

  /**
   * Gaussian Mixture configurations for individual model-fitting rounds.
   */
  private var gmConfigurations: Iterable[GmConfig] = _

  /**
   * Random seed for a model-fitting round. Generally remains unchanged, unless
   * [[randomizeGmSeed]] is set to `true`.
   */
  private var gmSeedBase: Int = 159147643

  /**
   * Enables generating a new random seed for each model-fitting round.
   * Primarily for debugging purposes when finding a new seed for model-fitting.
   */
  private val randomizeGmSeed: Boolean = false

  /**
   * Random generator for the seed used in model-fitting rounds.
   * Only used when [[randomizeGmSeed]] is `true`.
   */
  private val gmSeedRandom: Random = new Random()

  private def prepareInput(
    pointCount: Int,
    dimensionCount: Int,
    clusterCount: Int,
    clusterDistance: Int
  ): Seq[(Point, Point)] = {
    // TODO: Use a Renaissance-provided random generator.
    val rand = new Random(524764901)

    def randGauss(scale: Double): Double = {
      rand.nextGaussian() * scale
    }

    def makeCentroids(clusterCount: Int, dimensionCount: Int): Seq[Array[Double]] = {
      // Generate cluster centers with increasing offset from vertices of a hypercube.
      (0 until clusterCount).map { clusterIndex =>
        (0 until dimensionCount).map { dimensionIndex =>
          ((clusterIndex >> dimensionIndex) % 2) * (clusterDistance + clusterIndex * 0.8)
        }.toArray
      }
    }

    assert(
      clusterCount <= (1 << dimensionCount),
      "The cluster count should be less than or equal to 2 raised to the power of the dimension count."
    )

    val centroids = makeCentroids(clusterCount, dimensionCount)

    // Scale an N(0,1) gaussian so that most points (expressed as a multiple of standard
    // deviation) of the last centroid fall within half the centroid "distance". The limit
    // is proportionally lower for centroids with lower indices.
    val sigmaCount = 3
    val scaleMax = (clusterDistance / 2.0) / sigmaCount
    val scaleFraction = scaleMax / centroids.length

    (0 until pointCount).map { pointIndex =>
      val centroidIndex = pointIndex % centroids.length
      val centroid = centroids(centroidIndex)
      val point = centroid.indices.map { dimension =>
        centroid(dimension) + randGauss((centroidIndex + 1) * scaleFraction)
      }.toArray

      (Vectors.dense(point), Vectors.dense(centroid))
    }
  }

  private def splitAt[T](xs: Seq[T], splitPoints: Double*) = {
    assert(
      !splitPoints.exists(p => p <= 0.0 || p >= 1.0),
      "Split points must be between 0 and 1 (exclusive)."
    )

    val length = xs.length
    val indices = (0 +: splitPoints.map(p => (p * length).toInt) :+ length).distinct.sorted

    indices
      .sliding(2)
      .map {
        case Seq(start, end) =>
          xs.slice(start, end)
      }
      .toSeq
  }

  private def parallelizePoints(pointsWithCentroids: Seq[(Point, Point)]) = {
    val points = pointsWithCentroids.map { case (point, _) => point }
    sparkContext.parallelize(points)
  }

  private def parallelizeCentroids(pointsWithCentroids: Seq[(Point, Point)]) = {
    val centroids = pointsWithCentroids.map { case (_, centroid) => centroid }
    sparkContext.parallelize(centroids)
  }

  override def setUpBeforeAll(bc: BenchmarkContext): Unit = {
    setUpSparkContext(bc)

    // Validation parameters.
    predictionTolerance = bc.parameter("prediction_tolerance").toDouble
    expectedModelAccuracy = bc.parameter("expected_model_accuracy").toDouble

    // Generate input points.
    val clusterCount = bc.parameter("cluster_count").toPositiveInteger
    val inputPointsWithCentroids = prepareInput(
      bc.parameter("point_count").toPositiveInteger,
      bc.parameter("dimension_count").toPositiveInteger,
      clusterCount,
      bc.parameter("cluster_distance").toPositiveInteger
    )

    // Split input points into training (80%), validation (10%), and testing (10%) sets.
    val Seq(training, validation, testing) = splitAt(inputPointsWithCentroids, 0.8, 0.9)
    trainingPoints = ensureCached(parallelizePoints(training))
    validationPoints = ensureCached(parallelizePoints(validation))
    validationCentroids = ensureCached(parallelizeCentroids(validation))
    testingPoints = ensureCached(parallelizePoints(testing))
    testingCentroids = ensureCached(parallelizeCentroids(validation))

    // GM algorithm parameters.
    import scala.jdk.CollectionConverters._

    gmConfigurations = bc
      .parameter("gm_configs")
      .toCsvRows(row =>
        GmConfig(
          row.get("model_count").toInt,
          // Use more gaussians than clusters to improve fitting.
          (row.get("gaussians_per_cluster").toDouble * clusterCount).toInt,
          row.get("iteration_count").toInt
        )
      )
      .asScala
  }

  override def setUpBeforeEach(context: BenchmarkContext): Unit = {
    if (randomizeGmSeed) {
      gmSeedBase = gmSeedRandom.nextInt()
    }
  }

  private def computeModelAccuracy(
    model: GaussianMixtureModel,
    points: RDD[Point],
    expectedCentroids: RDD[Point]
  ): Double = {
    def isAccurate(predictedCentroid: Point, expectedCentroid: Point, tolerance: Double) = {
      Vectors.sqdist(predictedCentroid, expectedCentroid) <= tolerance
    }

    // Turn the tolerance parameter into a local constant so that it can be captured.
    val tolerance = predictionTolerance

    val predictedCentroids = model.predict(points).map(index => model.gaussians(index).mu)
    val accuratePredictionCount = predictedCentroids
      .zip(expectedCentroids)
      .filter(centroids => isAccurate(centroids._1, centroids._2, tolerance))
      .count()

    accuratePredictionCount.toDouble / points.count()
  }

  private def trainModels(): GaussianMixtureModel = {
    var bestModel: GaussianMixtureModel = null
    var bestAccuracy: Double = 0.0

    for (config <- gmConfigurations) {
      for (i <- 0 until config.modelCount) {
        val seed = gmSeedBase + i
        val gaussMix = new GaussianMixture()
          .setK(config.gaussianCount)
          .setMaxIterations(config.iterationCount)
          .setSeed(seed)
          .setConvergenceTol(0)

        val model = gaussMix.run(trainingPoints)
        val accuracy = computeModelAccuracy(model, validationPoints, validationCentroids)

        println(
          f"Accuracy (validation) = ${accuracy}%.5f for the model trained with " +
            s"K = ${config.gaussianCount}, maxIterations = ${config.iterationCount}, and seed = ${seed}."
        )

        if (accuracy >= bestAccuracy) {
          bestModel = model
          bestAccuracy = accuracy
        }
      }
    }

    bestModel
  }

  override def run(bc: BenchmarkContext): BenchmarkResult = {
    val bestModel = trainModels()
    val bestModelAccuracy = computeModelAccuracy(bestModel, testingPoints, testingCentroids)

    () => {
      if (bestModelAccuracy < expectedModelAccuracy) {
        throw new ValidationException(
          s"Expected model accuracy of at least ${expectedModelAccuracy} but got ${bestModelAccuracy}"
        )
      }
    }
  }

  override def tearDownAfterAll(bc: BenchmarkContext): Unit = {
    tearDownSparkContext()
  }
}
