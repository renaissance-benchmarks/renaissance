package org.renaissance.apache.spark

import org.apache.spark.ml.classification.LogisticRegression
import org.apache.spark.ml.classification.LogisticRegressionModel
import org.apache.spark.sql.DataFrame
import org.renaissance.Benchmark
import org.renaissance.Benchmark._
import org.renaissance.BenchmarkContext
import org.renaissance.BenchmarkResult
import org.renaissance.BenchmarkResult.Assert
import org.renaissance.License
import org.renaissance.apache.spark.ResourceUtil.duplicateLinesFromUrl

import java.nio.file.Path

@Name("log-regression")
@Group("apache-spark")
@Summary("Runs the Logistic Regression algorithm from the Spark ML library.")
@Licenses(Array(License.APACHE2))
@Repetitions(20)
@Parameter(
  name = "spark_thread_limit",
  defaultValue = "12",
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
@Parameter(name = "expected_coefficient_sum", defaultValue = "-0.0653998570980114")
@Parameter(name = "expected_coefficient_sum_squares", defaultValue = "9.401759355004592E-5")
@Parameter(name = "expected_intercept_value", defaultValue = "2.287050116462375")
@Parameter(name = "expected_intercept_count", defaultValue = "1")
@Parameter(name = "expected_class_count", defaultValue = "2")
@Configuration(
  name = "test",
  settings = Array(
    "copy_count = 5",
    "expected_coefficient_sum = -0.06538768469885561",
    "expected_coefficient_sum_squares = 9.395555567324299E-5",
    "expected_intercept_value = 2.286718680950285",
    "expected_class_count = 2"
  )
)
@Configuration(name = "jmh")
final class LogRegression extends Benchmark with SparkUtil {

  // Utility class for validation.

  private case class ModelSummary(
    coefficientSum: Double,
    coefficientSumSquares: Double,
    coefficientCount: Int,
    interceptValue: Double,
    interceptCount: Int,
    classCount: Int
  )

  // TODO: Consolidate benchmark parameters across the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/27

  private val inputResource = "/sample_libsvm_data.txt"

  private val inputFeatureCount = 692

  private val lrRegularizationParam = 0.1

  private val lrElasticNetMixingParam = 0.0

  private val lrConvergenceToleranceParam = 0.0

  private var lrMaxIterationsParam: Int = _

  private var expectedModelSummary: ModelSummary = _

  private var inputDataFrame: DataFrame = _

  private def loadData(inputFile: Path, featureCount: Int) = {
    sparkSession.read
      .format("libsvm")
      .option("numFeatures", featureCount)
      .load(inputFile.toString)
  }

  override def setUpBeforeAll(bc: BenchmarkContext): Unit = {
    setUpSparkContext(bc)

    lrMaxIterationsParam = bc.parameter("max_iterations").toPositiveInteger

    // Validation parameters.
    expectedModelSummary = ModelSummary(
      bc.parameter("expected_coefficient_sum").toDouble,
      bc.parameter("expected_coefficient_sum_squares").toDouble,
      inputFeatureCount,
      bc.parameter("expected_intercept_value").toDouble,
      bc.parameter("expected_intercept_count").toPositiveInteger,
      bc.parameter("expected_class_count").toPositiveInteger
    )

    val inputFile = duplicateLinesFromUrl(
      getClass.getResource(inputResource),
      bc.parameter("copy_count").toPositiveInteger,
      bc.scratchDirectory().resolve("input.txt")
    )

    inputDataFrame = ensureCached(loadData(inputFile, inputFeatureCount))
  }

  override def run(bc: BenchmarkContext): BenchmarkResult = {
    val logRegression = new LogisticRegression()
      .setElasticNetParam(lrElasticNetMixingParam)
      .setRegParam(lrRegularizationParam)
      .setTol(lrConvergenceToleranceParam)
      .setMaxIter(lrMaxIterationsParam)

    val logRegressionModel = logRegression.fit(inputDataFrame)
    () => validate(logRegressionModel)
  }

  private def validate(model: LogisticRegressionModel): Unit = {
    //
    // Validation currently supports only binary classification which returns
    // a single intercept value. If multinomial logistic regression is needed,
    // the validation needs to be updated to support multiple intercept values.
    //
    val actualModelSummary = summarizeModel(model)
    validateSummary(
      expectedModelSummary,
      actualModelSummary,
      coefficientSumTolerance = 0.1e-14,
      coefficientSumSquaresTolerance = 0.1e-17,
      interceptTolerance = 0.1e-13
    )
  }

  private def summarizeModel(model: LogisticRegressionModel): ModelSummary = {
    val coefficients = model.coefficients.toArray

    ModelSummary(
      coefficients.sum,
      coefficients.map(num => num * num).sum,
      coefficients.length,
      model.interceptVector(0),
      model.interceptVector.size,
      model.numClasses
    )
  }

  private def validateSummary(
    expected: ModelSummary,
    actual: ModelSummary,
    coefficientSumTolerance: Double,
    coefficientSumSquaresTolerance: Double,
    interceptTolerance: Double
  ): Unit = {
    Assert.assertEquals(
      expected.coefficientSum,
      actual.coefficientSum,
      coefficientSumTolerance,
      "coefficients sum"
    )

    Assert.assertEquals(
      expected.coefficientSumSquares,
      actual.coefficientSumSquares,
      coefficientSumSquaresTolerance,
      "coefficients sum of squares"
    )

    Assert.assertEquals(expected.coefficientCount, actual.coefficientCount, "coefficient count")

    Assert.assertEquals(
      expected.interceptValue,
      actual.interceptValue,
      interceptTolerance,
      "intercept value"
    )

    Assert.assertEquals(expected.interceptCount, actual.interceptCount, "intercept count")

    Assert.assertEquals(expected.classCount, actual.classCount, "class count")
  }

  override def tearDownAfterAll(bc: BenchmarkContext): Unit = {
    tearDownSparkContext()
  }
}
