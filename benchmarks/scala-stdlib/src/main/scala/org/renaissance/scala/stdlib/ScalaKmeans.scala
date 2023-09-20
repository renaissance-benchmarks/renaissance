package org.renaissance.scala.stdlib

import org.renaissance.Benchmark
import org.renaissance.Benchmark._
import org.renaissance.BenchmarkContext
import org.renaissance.BenchmarkResult
import org.renaissance.BenchmarkResult.Assert
import org.renaissance.License

import scala.collection._
import scala.util.Random

trait KmeansUtilities {

  class Point(val x: Double, val y: Double, val z: Double) {
    private def square(v: Double): Double = v * v
    private def round(v: Double): Double = (v * 100).toInt / 100.0

    def squareDistance(that: Point): Double = {
      square(that.x - x) + square(that.y - y) + square(that.z - z)
    }
    override def toString = s"(${round(x)}, ${round(y)}, ${round(z)})"
  }

  def generatePoints(k: Int, pointsCount: Int): Seq[Point] = {
    val randX = new Random(1)
    val randY = new Random(3)
    val randZ = new Random(5)
    (0 until pointsCount).map({ i =>
      val x = ((i + 1) % k) * 1.0 / k + randX.nextDouble() * 0.5
      val y = ((i + 5) % k) * 1.0 / k + randY.nextDouble() * 0.5
      val z = ((i + 7) % k) * 1.0 / k + randZ.nextDouble() * 0.5
      new Point(x, y, z)
    })
  }

  def initializeMeans(k: Int, points: Seq[Point]): Seq[Point] = {
    val rand = new Random(7)
    (0 until k)
      .map(_ => points(rand.nextInt(points.length)))
  }

  def findClosest(p: Point, means: Seq[Point]): Point = {
    assert(means.nonEmpty)
    var minDistance = p.squareDistance(means(0))
    var closest = means(0)
    for (mean <- means) {
      val distance = p.squareDistance(mean)
      if (distance < minDistance) {
        minDistance = distance
        closest = mean
      }
    }
    closest
  }

  def classify(
    points: Seq[Point],
    means: Seq[Point]
  ): Map[Point, Seq[Point]] = {
    val grouped = points.groupBy(p => findClosest(p, means))

    // Add "unused" means to the result.
    means.foldLeft(grouped) { (map, mean) =>
      if (map.contains(mean)) map else map.updated(mean, Seq())
    }
  }

  def findAverage(oldMean: Point, points: Seq[Point]): Point =
    if (points.isEmpty) oldMean
    else {
      var x = 0.0
      var y = 0.0
      var z = 0.0
      points.foreach { p =>
        x += p.x
        y += p.y
        z += p.z
      }
      new Point(x / points.length, y / points.length, z / points.length)
    }

  def updateMeans(
    classified: Map[Point, Seq[Point]],
    oldMeans: Seq[Point]
  ): Seq[Point] = {
    oldMeans.map(mean => findAverage(mean, classified(mean)))
  }

  def converged(eta: Double)(
    oldMeans: Seq[Point],
    newMeans: Seq[Point]
  ): Boolean = {
    (oldMeans zip newMeans)
      .map({
        case (oldMean, newMean) =>
          oldMean squareDistance newMean
      })
      .forall(_ <= eta)
  }

  @annotation.tailrec
  final def kMeans(
    points: Seq[Point],
    means: Seq[Point],
    eta: Double
  ): Seq[Point] = {
    val classifiedPoints = classify(points, means)

    val newMeans = updateMeans(classifiedPoints, means)

    if (!converged(eta)(means, newMeans)) {
      kMeans(points, newMeans, eta)
    } else {
      newMeans
    }
  }
}

@Name("scala-kmeans")
@Group("scala-stdlib")
@Group("scala") // With Scala 3, the primary group goes last.
@Summary("Runs the K-Means algorithm using Scala collections.")
@Licenses(Array(License.MIT))
@Repetitions(50)
@Parameter(
  name = "point_count",
  defaultValue = "500000",
  summary = "Number of data points to generate"
)
@Parameter(
  name = "cluster_count",
  defaultValue = "32",
  summary = "Number of clusters to create"
)
@Configuration(name = "test", settings = Array("point_count = 5000", "cluster_count = 8"))
@Configuration(name = "jmh")
final class ScalaKmeans extends Benchmark with KmeansUtilities {

  // TODO: Consolidate benchmark parameters across the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/27

  private var pointCountParam: Int = _

  private var clusterCountParam: Int = _

  private val eta = 0.01

  private var points: Seq[Point] = _

  private var means: Seq[Point] = _

  private val EXPECTED_RESULT_FULL = Seq(
    new Point(0.69, 0.54, 0.76),
    new Point(0.97, 1.09, 0.37),
    new Point(0.89, 1.00, 0.75),
    new Point(1.13, 0.18, 0.19),
    new Point(0.34, 0.36, 0.68),
    new Point(0.56, 0.88, 0.70),
    new Point(0.46, 0.47, 0.36),
    new Point(0.53, 0.72, 0.88),
    new Point(0.38, 0.62, 0.77),
    new Point(0.78, 0.75, 0.66),
    new Point(0.26, 0.66, 0.57),
    new Point(0.92, 0.81, 0.89),
    new Point(0.79, 0.89, 1.22),
    new Point(0.74, 0.71, 1.01),
    new Point(0.32, 0.38, 0.45),
    new Point(1.30, 0.41, 0.49),
    new Point(0.16, 0.54, 0.36),
    new Point(0.83, 1.11, 1.00),
    new Point(0.73, 0.95, 0.88),
    new Point(0.53, 0.56, 0.56),
    new Point(1.04, 0.87, 1.16),
    new Point(0.62, 0.98, 1.05),
    new Point(0.17, 0.26, 0.42),
    new Point(1.21, 0.15, 0.45),
    new Point(1.01, 0.36, 0.41),
    new Point(1.01, 1.16, 1.31),
    new Point(1.09, 1.04, 0.99),
    new Point(1.16, 1.24, 1.22),
    new Point(0.84, 1.10, 1.22),
    new Point(0.98, 1.26, 1.02),
    new Point(1.25, 0.43, 0.22),
    new Point(1.11, 1.23, 0.23)
  )

  private val EXPECTED_RESULT_TEST = Seq(
    new Point(0.91, 0.51, 0.66),
    new Point(0.78, 0.34, 0.41),
    new Point(1.18, 0.43, 0.71),
    new Point(0.99, 0.48, 0.94),
    new Point(0.75, 0.19, 0.61),
    new Point(1.12, 0.74, 0.89),
    new Point(0.31, 0.82, 1.06),
    new Point(0.56, 1.05, 0.31)
  )

  private var expectedResult: Seq[Point] = _

  override def setUpBeforeAll(c: BenchmarkContext): Unit = {
    pointCountParam = c.parameter("point_count").toPositiveInteger
    clusterCountParam = c.parameter("cluster_count").toPositiveInteger

    if (EXPECTED_RESULT_FULL.length == clusterCountParam) {
      expectedResult = EXPECTED_RESULT_FULL
    } else if (EXPECTED_RESULT_TEST.length == clusterCountParam) {
      expectedResult = EXPECTED_RESULT_TEST
    } else {
      throw new AssertionError(s"no expected result for $clusterCountParam clusters")
    }

    points = generatePoints(clusterCountParam, pointCountParam)
    means = initializeMeans(clusterCountParam, points)
  }

  private def validate(expected: Seq[Point], actual: Seq[Point]): Unit = {
    val EPSILON = 0.01

    Assert.assertEquals(expected.length, actual.length, "centers count")

    for (idx <- expected.indices) {
      val (exp, act) = (expected(idx), actual(idx))

      Assert.assertEquals(exp.x, act.x, EPSILON, s"center $idx position at x")
      Assert.assertEquals(exp.y, act.y, EPSILON, s"center $idx position at y")
      Assert.assertEquals(exp.z, act.z, EPSILON, s"center $idx position at z")
    }
  }

  override def run(c: BenchmarkContext): BenchmarkResult = {
    val result = kMeans(points, means, eta)
    () => validate(expectedResult, result)
  }
}
