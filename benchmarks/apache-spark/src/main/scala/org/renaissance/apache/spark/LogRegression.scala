package org.renaissance.apache.spark

import org.apache.spark.ml.classification.LogisticRegression
import org.apache.spark.ml.classification.LogisticRegressionModel
import org.apache.spark.ml.linalg.Vectors
import org.apache.spark.rdd.RDD
import org.apache.spark.sql._
import org.renaissance.Benchmark
import org.renaissance.Benchmark._
import org.renaissance.BenchmarkContext
import org.renaissance.BenchmarkResult
import org.renaissance.BenchmarkResult.Validators
import org.renaissance.License

import java.io.BufferedReader
import java.io.InputStreamReader
import java.nio.file.Files
import java.nio.file.Path
import java.nio.file.StandardOpenOption
import java.util.stream.Collectors

@Name("log-regression")
@Group("apache-spark")
@Summary("Runs the logistic regression workload from the Spark MLlib.")
@Licenses(Array(License.APACHE2))
@Repetitions(20)
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
  name = "copy_count",
  defaultValue = "400",
  summary = "Number of sample data copies to make in the input data."
)
@Parameter(
  name = "max_iterations",
  defaultValue = "20",
  summary = "Maximum number of iterations of the logistic regression algorithm."
)
@Configuration(name = "test", settings = Array("copy_count = 5"))
@Configuration(name = "jmh")
final class LogRegression extends Benchmark with SparkUtil {

  // TODO: Consolidate benchmark parameters across the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/27

  private val inputResource = "/sample_libsvm_data.txt"

  private var maxIterationsParam: Int = _

  private val lrRegularizationParam = 0.1

  private val lrElasticNetMixingParam = 0.0

  private val lrConvergenceToleranceParam = 0.0

  private var inputTuples: RDD[(Double, org.apache.spark.ml.linalg.Vector)] = _

  private var outputLogisticRegression: LogisticRegressionModel = _

  private def prepareInput(resourcePath: String, copyCount: Int, outputFile: Path): Path = {
    def loadInputResource() = {
      val resourceStream = getClass.getResourceAsStream(resourcePath)
      val reader = new BufferedReader(new InputStreamReader(resourceStream))
      reader.lines().collect(Collectors.toList())
    }

    val lines = loadInputResource()
    for (_ <- 0 until copyCount) {
      Files.write(outputFile, lines, StandardOpenOption.CREATE, StandardOpenOption.APPEND)
    }

    outputFile
  }

  private def loadData(inputFile: Path) = {
    val featureCount = 692

    sparkContext
      .textFile(inputFile.toString)
      .map { line =>
        val parts = line.split(" ")
        val features = new Array[Double](featureCount)
        parts.tail.foreach { part =>
          val dimval = part.split(":")
          val index = dimval(0).toInt - 1
          val value = dimval(1).toInt
          features(index) = value
        }
        (parts(0).toDouble, Vectors.dense(features))
      }
      .cache()
  }

  override def setUpBeforeAll(bc: BenchmarkContext): Unit = {
    setUpSparkContext(bc)

    maxIterationsParam = bc.parameter("max_iterations").toPositiveInteger

    val inputFile = prepareInput(
      inputResource,
      bc.parameter("copy_count").toPositiveInteger,
      bc.scratchDirectory().resolve("input.txt")
    )

    inputTuples = ensureCached(loadData(inputFile))
  }

  override def run(bc: BenchmarkContext): BenchmarkResult = {
    val lor = new LogisticRegression()
      .setElasticNetParam(lrElasticNetMixingParam)
      .setRegParam(lrRegularizationParam)
      .setTol(lrConvergenceToleranceParam)
      .setMaxIter(maxIterationsParam)

    val sqlContext = new SQLContext(inputTuples.context)
    import sqlContext.implicits._
    outputLogisticRegression = lor.fit(inputTuples.toDF("label", "features"))

    // TODO: add more in-depth validation
    Validators.compound(
      Validators.simple("class count", 2, outputLogisticRegression.numClasses),
      Validators.simple("feature count", 692, outputLogisticRegression.numFeatures)
    )
  }

  override def tearDownAfterAll(bc: BenchmarkContext): Unit = {
    val outputFile = bc.scratchDirectory().resolve("output.txt")
    dumpResult(outputLogisticRegression, outputFile)

    tearDownSparkContext()
  }

  private def dumpResult(lrm: LogisticRegressionModel, outputFile: Path) = {
    val output = new StringBuilder
    output.append(s"num features: ${lrm.numFeatures}\n")
    output.append(s"num classes: ${lrm.numClasses}\n")
    output.append(s"intercepts: ${lrm.interceptVector.toString}\n")
    output.append(s"coefficients: ${lrm.coefficients.toString}\n")

    // Files.writeString() is only available from Java 11.
    Files.write(outputFile, output.toString.getBytes)
  }

}
