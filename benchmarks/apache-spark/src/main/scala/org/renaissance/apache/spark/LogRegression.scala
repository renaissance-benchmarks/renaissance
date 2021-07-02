package org.renaissance.apache.spark

import org.apache.spark.ml.classification.LogisticRegression
import org.apache.spark.ml.classification.LogisticRegressionModel
import org.apache.spark.sql.DataFrame
import org.renaissance.Benchmark
import org.renaissance.Benchmark._
import org.renaissance.BenchmarkContext
import org.renaissance.BenchmarkResult
import org.renaissance.BenchmarkResult.Validators
import org.renaissance.License
import org.renaissance.apache.spark.ResourceUtil.duplicateLinesFromUrl

import java.nio.file.Files
import java.nio.file.Path

@Name("log-regression")
@Group("apache-spark")
@Summary("Runs the Logistic Regression algorithm from the Spark ML library.")
@Licenses(Array(License.APACHE2))
@Repetitions(20)
@Parameter(
  name = "spark_thread_limit",
  defaultValue = "$cpu.count",
  summary = "Maximum number of threads for the Spark local executor."
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

  private val inputFeatureCount = 692

  private var maxIterationsParam: Int = _

  private val lrRegularizationParam = 0.1

  private val lrElasticNetMixingParam = 0.0

  private val lrConvergenceToleranceParam = 0.0

  private var inputDataFrame: DataFrame = _

  private var outputLogisticRegression: LogisticRegressionModel = _

  private def loadData(inputFile: Path, featureCount: Int) = {
    sparkSession.read
      .format("libsvm")
      .option("numFeatures", featureCount)
      .load(inputFile.toString)
  }

  override def setUpBeforeAll(bc: BenchmarkContext): Unit = {
    setUpSparkContext(bc)

    maxIterationsParam = bc.parameter("max_iterations").toPositiveInteger

    val inputFile = duplicateLinesFromUrl(
      getClass.getResource(inputResource),
      bc.parameter("copy_count").toPositiveInteger,
      bc.scratchDirectory().resolve("input.txt")
    )

    inputDataFrame = ensureCached(loadData(inputFile, inputFeatureCount))
  }

  override def run(bc: BenchmarkContext): BenchmarkResult = {
    val lor = new LogisticRegression()
      .setElasticNetParam(lrElasticNetMixingParam)
      .setRegParam(lrRegularizationParam)
      .setTol(lrConvergenceToleranceParam)
      .setMaxIter(maxIterationsParam)

    outputLogisticRegression = lor.fit(inputDataFrame)

    // TODO: add more in-depth validation
    Validators.compound(
      Validators.simple("class count", 2, outputLogisticRegression.numClasses),
      Validators.simple(
        "feature count",
        inputFeatureCount,
        outputLogisticRegression.numFeatures
      )
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
