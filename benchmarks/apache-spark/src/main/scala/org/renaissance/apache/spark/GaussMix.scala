package org.renaissance.apache.spark

import java.nio.charset.StandardCharsets
import java.nio.file.Paths

import org.apache.commons.io.FileUtils
import org.apache.spark.SparkContext
import org.apache.spark.mllib.clustering.GaussianMixture
import org.apache.spark.mllib.clustering.GaussianMixtureModel
import org.apache.spark.mllib.linalg.Vectors
import org.apache.spark.rdd.RDD
import org.renaissance.Benchmark
import org.renaissance.Benchmark._
import org.renaissance.BenchmarkContext
import org.renaissance.BenchmarkResult
import org.renaissance.BenchmarkResult.Validators
import org.renaissance.License

import scala.util.Random

@Name("gauss-mix")
@Group("apache-spark")
@Summary("Computes a Gaussian mixture model using expectation-maximization.")
@Licenses(Array(License.APACHE2))
@Repetitions(40)
@Parameter(name = "thread_count", defaultValue = "$cpu.count")
@Parameter(name = "number_count", defaultValue = "15000")
@Parameter(
  name = "max_iterations",
  defaultValue = "15",
  summary = "The maximum number of iterations allowed"
)
@Configuration(name = "test", settings = Array("number_count = 7", "max_iterations = 3"))
@Configuration(name = "jmh")
final class GaussMix extends Benchmark with SparkUtil {

  // TODO: Consolidate benchmark parameters across the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/27

  private var threadCountParam: Int = _

  private var numberCountParam: Int = _

  private var maxIterationsParam: Int = _

  private val DISTRIBUTION_COUNT = 6

  private val COMPONENTS = 10

  val gaussMixPath = Paths.get("target", "gauss-mix")

  val outputPath = gaussMixPath.resolve("output")

  val measurementsFile = gaussMixPath.resolve("measurements.txt")

  var sc: SparkContext = _

  var gmm: GaussianMixtureModel = _

  var input: RDD[org.apache.spark.mllib.linalg.Vector] = _

  override def setUpBeforeAll(c: BenchmarkContext): Unit = {
    threadCountParam = c.parameter("thread_count").toPositiveInteger
    numberCountParam = c.parameter("number_count").toPositiveInteger
    maxIterationsParam = c.parameter("max_iterations").toPositiveInteger

    val tempDirPath = c.scratchDirectory()
    sc = setUpSparkContext(tempDirPath, threadCountParam, "gauss-mix")
    prepareInput()
    loadData()
    ensureCaching(input)
  }

  def prepareInput() = {
    FileUtils.deleteDirectory(gaussMixPath.toFile)
    val rand = new Random(0L)
    val content = new StringBuilder
    for (i <- 0 until numberCountParam) {
      def randDouble(): Double = {
        (rand.nextDouble() * 10).toInt / 10.0
      }
      content.append((0 until COMPONENTS).map(_ => randDouble()).mkString(" "))
      content.append("\n")
    }
    FileUtils.write(measurementsFile.toFile, content, StandardCharsets.UTF_8, true)
  }

  def loadData(): Unit = {
    input = sc
      .textFile(measurementsFile.toString)
      .map { line =>
        val raw = line.split(" ").map(_.toDouble)
        Vectors.dense(raw)
      }
      .cache()
  }

  override def tearDownAfterAll(c: BenchmarkContext) = {
    val output = gmm.gaussians.mkString(", ")
    FileUtils.write(outputPath.toFile, output, StandardCharsets.UTF_8, true)
    tearDownSparkContext(sc)
  }

  override def run(c: BenchmarkContext): BenchmarkResult = {
    gmm = new GaussianMixture()
      .setK(DISTRIBUTION_COUNT)
      .setMaxIterations(maxIterationsParam)
      .run(input)

    // TODO: add more in-depth validation
    Validators.simple("number of gaussians", 6, gmm.k)
  }

}
