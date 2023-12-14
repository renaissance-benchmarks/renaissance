package org.renaissance.jdk.concurrent

import org.renaissance.Benchmark
import org.renaissance.Benchmark._
import org.renaissance.BenchmarkContext
import org.renaissance.BenchmarkResult
import org.renaissance.BenchmarkResult.Assert
import org.renaissance.BenchmarkResult.ValidationException
import org.renaissance.License

@Name("fj-kmeans")
@Group("jdk-concurrent")
@Group("concurrency") // With Scala 3, the primary group goes last.
@Summary("Runs the K-Means algorithm using the fork/join framework.")
@Licenses(Array(License.APACHE2))
@Repetitions(30)
@Parameter(name = "thread_count", defaultValue = "$cpu.count")
@Parameter(name = "vector_length", defaultValue = "500000")
@Parameter(
  name = "expected_points",
  defaultValue =
    "coordinate0, coordinate1, coordinate2, coordinate3, coordinate4;" +
      "0.25082639502459003, 0.6497486071544945, 1.0510364066500688, 0.4495645173146992, 0.8501539091801917;" +
      "0.4295733401344313, 0.7923331044052437, 0.33748651607683705, 0.616584488812924, 0.9940841920765144;" +
      "0.4699709750298814, 0.9068435238683682, 0.16329156616644577, 0.6836090279311271, 1.106207472898731;" +
      "0.6502903900584982, 1.0467507844172892, 0.45007025858919064, 0.8508674384544423, 0.2502136005169379;" +
      "0.9506910376732071, 0.3501229839992895, 0.7504274700852247, 0.6498870085787202, 0.5508637399619365;"
)
@Configuration(
  name = "test",
  settings = Array(
    "vector_length = 500",
    "expected_points = " +
      "coordinate0, coordinate1, coordinate2, coordinate3, coordinate4;" +
      "0.24747990375773235, 0.683753811312102, 1.059932089170533, 0.4412059965758913, 0.8323842734657464;" +
      "0.39754906356387437, 0.849757386902491, 0.2597990838016599, 0.7036740738069435, 1.12204910354274;" +
      "0.5387943186874504, 0.8549624519329776, 0.22868027524646195, 0.6115150748275184, 0.863010675587644;" +
      "0.7453633652450244, 0.6266833045600323, 0.5673388726440936, 0.9691716314403028, 0.3405964300261378;" +
      "1.0603556317665093, 0.458971035483256, 0.8731248243330151, 0.24674022819877325, 0.6908940170485317;"
  )
)
@Configuration(name = "jmh")
final class FjKmeans extends Benchmark {

  // TODO: Consolidate benchmark parameters across the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/27

  private var threadCountParam: Int = _

  private var vectorLengthParam: Int = _

  private val DIMENSION = 5

  private val CLUSTER_COUNT = 5

  private val ITERATION_COUNT = 50

  private val LOOP_COUNT = 4

  private var benchmark: JavaKMeans = _

  private var data: java.util.List[Array[java.lang.Double]] = _

  private var expectedPoints: Seq[Array[Double]] = _

  override def setUpBeforeAll(c: BenchmarkContext): Unit = {
    import scala.jdk.CollectionConverters.ListHasAsScala

    def rowToArray(row: java.util.Map[String, String]): Array[Double] = {
      (0 until row.size()).map(i => row.get(s"coordinate$i").toDouble).toArray
    }

    threadCountParam = c.parameter("thread_count").toInteger
    vectorLengthParam = c.parameter("vector_length").toInteger
    expectedPoints = c.parameter("expected_points").toCsvRows(rowToArray(_)).asScala.toSeq

    benchmark = new JavaKMeans(DIMENSION, threadCountParam)
    data = JavaKMeans.generateData(vectorLengthParam, DIMENSION, CLUSTER_COUNT)
  }

  private def assertEqualCenters(
    expected: Array[Double],
    actual: Array[java.lang.Double],
    epsilon: Double,
    subject: String
  ): Unit = {
    import scala.math.abs

    Assert.assertEquals(expected.length, actual.length, s"$subject dimension count")

    // Find index for which the difference between [[expected]] and [[actual]] exceeds [[epsilon]].
    expected.indices.find(i => abs(expected(i) - actual(i)) > epsilon) match {
      case Some(index) =>
        throw new ValidationException(
          s"$subject, dimension $index: expected ${expected(index)} but got ${actual(index)}"
        )
      case None =>
    }
  }

  private def validate(
    expected: Seq[Array[Double]],
    results: IndexedSeq[java.util.List[Array[java.lang.Double]]]
  ): Unit = {
    import scala.jdk.CollectionConverters.ListHasAsScala

    val EPSILON: Double = 0.000001
    results.view.zipWithIndex.foreach {
      case (result, loopIndex) =>
        // Sort the centers by the first coordinate to get stable order.
        val actual = result.asScala.sortBy(_(0))

        Assert.assertEquals(expected.length, actual.length, s"loop $loopIndex center count")

        expected.lazyZip(actual).zipWithIndex.foreach {
          case ((expectedCenter, actualCenter), centerIndex) =>
            assertEqualCenters(
              expectedCenter,
              actualCenter,
              EPSILON,
              s"loop $loopIndex, center $centerIndex"
            )
        }
    }
  }

  override def run(c: BenchmarkContext): BenchmarkResult = {
    val results = for (_ <- 0 until LOOP_COUNT) yield {
      benchmark.run(CLUSTER_COUNT, data, ITERATION_COUNT)
    }

    () => validate(expectedPoints, results)
  }

  override def tearDownAfterAll(c: BenchmarkContext): Unit = {
    benchmark.tearDown()
    expectedPoints = null
    benchmark = null
    data = null
  }
}
