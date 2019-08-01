package org.renaissance.apache.spark

import java.nio.charset.StandardCharsets
import java.nio.file.Path
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
import org.renaissance.License

import scala.util.Random

@Name("gauss-mix")
@Group("apache-spark")
@Summary("Computes a Gaussian mixture model using expectation-maximization.")
@Licenses(Array(License.APACHE2))
@Repetitions(40)
final class GaussMix extends Benchmark with SparkUtil {

  // TODO: Consolidate benchmark parameters across the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/27

  val DISTRIBUTION_COUNT = 6

  val COMPONENTS = 10

  var SIZE = 15000

  var NUM_GMM_ITERATIONS = 15

  val THREAD_COUNT = Runtime.getRuntime.availableProcessors

  // TODO: Unify handling of scratch directories throughout the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/13

  val gaussMixPath = Paths.get("target", "gauss-mix")

  val outputPath = gaussMixPath.resolve("output")

  val measurementsFile = gaussMixPath.resolve("measurements.txt")

  var sc: SparkContext = null

  var gmm: GaussianMixtureModel = null

  var input: RDD[org.apache.spark.mllib.linalg.Vector] = null

  var tempDirPath: Path = null

  override def setUpBeforeAll(c: BenchmarkContext): Unit = {
    tempDirPath = c.generateTempDir("gauss_mix")
    sc = setUpSparkContext(tempDirPath, THREAD_COUNT, c.benchmarkName())
    if (c.functionalTest) {
      SIZE /= 2000
      NUM_GMM_ITERATIONS = 3
    }
    prepareInput()
    loadData()
  }

  def prepareInput() = {
    FileUtils.deleteDirectory(gaussMixPath.toFile)
    val rand = new Random(0L)
    val content = new StringBuilder
    for (i <- 0 until SIZE) {
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
    c.deleteTempDir(tempDirPath)
  }

  override def runIteration(c: BenchmarkContext): BenchmarkResult = {
    gmm = new GaussianMixture()
      .setK(DISTRIBUTION_COUNT)
      .setMaxIterations(NUM_GMM_ITERATIONS)
      .run(input)

    // TODO: add more in-depth validation
    BenchmarkResult.simple("number of gaussians", 6, gmm.k)
  }

}
