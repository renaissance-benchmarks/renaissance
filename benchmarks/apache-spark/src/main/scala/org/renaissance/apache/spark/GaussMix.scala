package org.renaissance.apache.spark

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

import java.nio.file.Files
import java.nio.file.Path
import scala.jdk.CollectionConverters.asJavaCollectionConverter
import scala.util.Random

@Name("gauss-mix")
@Group("apache-spark")
@Summary("Computes a Gaussian mixture model using expectation-maximization.")
@Licenses(Array(License.APACHE2))
@Repetitions(40)
@Parameter(
  name = "spark_executor_count",
  defaultValue = "4",
  summary = "Number of executor instances."
)
@Parameter(
  name = "spark_executor_thread_count",
  defaultValue = "$cpu.count",
  summary = "Number of threads per executor."
)
@Parameter(
  name = "point_count",
  defaultValue = "15000",
  summary = "Number of data points to generate."
)
@Parameter(
  name = "component_count",
  defaultValue = "10",
  summary = "Number of components in each data point."
)
@Parameter(
  name = "distribution_count",
  defaultValue = "6",
  summary = "Number of gaussian distributions in the mix."
)
@Parameter(
  name = "max_iterations",
  defaultValue = "15",
  summary = "Maximum number of iterations of the clustering algorithm."
)
@Configuration(name = "test", settings = Array("point_count = 7", "max_iterations = 3"))
@Configuration(name = "jmh")
final class GaussMix extends Benchmark with SparkUtil {

  // TODO: Consolidate benchmark parameters across the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/27

  private var maxIterationsParam: Int = _

  private var distributionCountParam: Int = _

  private var inputVectors: RDD[org.apache.spark.mllib.linalg.Vector] = _

  private var outputGaussianMixture: GaussianMixtureModel = _

  private def prepareInput(pointCount: Int, componentCount: Int, outputFile: Path): Path = {
    // TODO: Use a Renaissance-provided random generator.
    val rand = new Random(0L)

    def randDouble(): Double = {
      (rand.nextDouble() * 10).toInt / 10.0
    }

    val lines = (0 until pointCount).map { _ =>
      (0 until componentCount).map(_ => randDouble()).mkString(" ")
    }

    // Write output using UTF-8 encoding.
    Files.write(outputFile, lines.asJavaCollection)
  }

  private def loadData(inputFile: Path) = {
    sparkContext
      .textFile(inputFile.toString)
      .map { line =>
        val raw = line.split(" ").map(_.toDouble)
        Vectors.dense(raw)
      }
  }

  override def setUpBeforeAll(bc: BenchmarkContext): Unit = {
    setUpSparkContext(bc)

    maxIterationsParam = bc.parameter("max_iterations").toPositiveInteger
    distributionCountParam = bc.parameter("distribution_count").toPositiveInteger

    val inputFile = prepareInput(
      bc.parameter("point_count").toPositiveInteger,
      bc.parameter("component_count").toPositiveInteger,
      bc.scratchDirectory().resolve("input.txt")
    )

    inputVectors = ensureCached(loadData(inputFile))
  }

  override def run(bc: BenchmarkContext): BenchmarkResult = {
    outputGaussianMixture = new GaussianMixture()
      .setK(distributionCountParam)
      .setMaxIterations(maxIterationsParam)
      .setSeed(159147643)
      .run(inputVectors)

    // TODO: add more in-depth validation
    Validators.simple("number of gaussians", distributionCountParam, outputGaussianMixture.k)
  }

  override def tearDownAfterAll(bc: BenchmarkContext) = {
    val outputFile = bc.scratchDirectory().resolve("output.txt")
    dumpResult(outputGaussianMixture, outputFile)

    tearDownSparkContext()
  }

  private def dumpResult(gmm: GaussianMixtureModel, outputFile: Path) = {
    val output = new StringBuilder
    gmm.gaussians
      .zip(gmm.weights)
      .zipWithIndex
      .foreach({
        case ((g, w), i) =>
          output.append(s"gaussian $i:\n")
          output.append(s"  weight: $w\n")
          output.append("  mu: ").append(g.mu).append("\n")
          output
            .append("  sigma: ")
            .append(g.sigma.rowIter.mkString("[", ", ", "]"))
            .append("\n\n")
      })

    // Files.writeString() is only available from Java 11.
    Files.write(outputFile, output.toString.getBytes)
  }

}
