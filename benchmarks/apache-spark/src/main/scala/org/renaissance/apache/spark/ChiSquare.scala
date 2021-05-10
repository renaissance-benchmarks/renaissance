package org.renaissance.apache.spark

import org.apache.spark.mllib.linalg.Vectors
import org.apache.spark.mllib.regression.LabeledPoint
import org.apache.spark.mllib.stat.Statistics
import org.apache.spark.mllib.stat.test.ChiSqTestResult
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

@Name("chi-square")
@Group("apache-spark")
@Summary("Runs the chi-square test from Spark MLlib.")
@Licenses(Array(License.APACHE2))
@Repetitions(60)
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
  defaultValue = "1500000",
  summary = "Number of data points to generate."
)
@Parameter(
  name = "component_count",
  defaultValue = "5",
  summary = "Number of components in each data point."
)
@Configuration(name = "test", settings = Array("point_count = 10000"))
@Configuration(name = "jmh")
final class ChiSquare extends Benchmark with SparkUtil {

  // TODO: Consolidate benchmark parameters across the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/27

  private var componentCountParam: Int = _

  private var inputPoints: RDD[LabeledPoint] = _

  private var outputTestResults: Array[ChiSqTestResult] = _

  private def prepareInput(pointCount: Int, componentCount: Int, outputFile: Path): Path = {
    // TODO: Use a Renaissance-provided random generator.
    val rand = new Random(0L)

    def randDouble(): Double = {
      (rand.nextDouble() * 10).toInt / 10.0
    }

    val line = new StringBuilder
    val lines = (0 until pointCount).map { _ =>
      line.clear()
      line.append(rand.nextInt(2))
      (0 until componentCount).map { _ =>
        line.append(" ").append(randDouble())
      }
      line.toString()
    }

    // Write output using UTF-8 encoding.
    Files.write(outputFile, lines.asJavaCollection)
  }

  private def loadData(inputFile: Path) = {
    sparkContext
      .textFile(inputFile.toString)
      .map { line =>
        val raw = line.split(" ").map(_.toDouble)
        new LabeledPoint(raw.head, Vectors.dense(raw.tail))
      }
      .cache()
  }

  override def setUpBeforeAll(bc: BenchmarkContext): Unit = {
    setUpSparkContext(bc)

    componentCountParam = bc.parameter("component_count").toPositiveInteger

    val inputFile = prepareInput(
      bc.parameter("point_count").toPositiveInteger,
      componentCountParam,
      bc.scratchDirectory().resolve("input.txt")
    )

    inputPoints = ensureCached(loadData(inputFile))
  }

  override def run(bc: BenchmarkContext): BenchmarkResult = {
    outputTestResults = Statistics.chiSqTest(inputPoints)

    // TODO: add more sophisticated validation
    Validators.simple("component count", componentCountParam, outputTestResults.size)
  }

  override def tearDownAfterAll(bc: BenchmarkContext): Unit = {
    val outputFile = bc.scratchDirectory().resolve("output.txt")
    dumpResult(outputTestResults, outputFile)

    tearDownSparkContext()
  }

  private def dumpResult(testResults: Array[ChiSqTestResult], outputFile: Path) = {
    val output = testResults.map(_.statistic).mkString(", ")
    // Files.writeString() is only available from Java 11.
    Files.write(outputFile, output.getBytes)
  }
}
