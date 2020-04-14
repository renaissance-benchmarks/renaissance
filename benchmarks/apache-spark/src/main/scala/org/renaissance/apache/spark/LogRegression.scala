package org.renaissance.apache.spark

import java.nio.charset.StandardCharsets
import java.nio.file.Path
import java.nio.file.Paths

import org.apache.commons.io.FileUtils
import org.apache.commons.io.IOUtils
import org.apache.spark.SparkContext
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

@Name("log-regression")
@Group("apache-spark")
@Summary("Runs the logistic regression workload from the Spark MLlib.")
@Licenses(Array(License.APACHE2))
@Repetitions(20)
// Work around @Repeatable annotations not working in this Scala version.
@Parameters(
  Array(
    new Parameter(name = "thread_count", defaultValue = "$cpu.count"),
    new Parameter(name = "copy_count", defaultValue = "400")
  )
)
@Configurations(
  Array(
    new Configuration(name = "test", settings = Array("copy_count = 5")),
    new Configuration(name = "jmh")
  )
)
final class LogRegression extends Benchmark with SparkUtil {

  // TODO: Consolidate benchmark parameters across the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/27

  private var threadCountParam: Int = _

  private var copyCountParam: Int = _

  private val REGULARIZATION_PARAM = 0.1

  private val MAX_ITERATIONS = 20

  private val ELASTIC_NET_PARAM = 0.0

  private val CONVERGENCE_TOLERANCE = 0.0

  // TODO: Unify handling of scratch directories throughout the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/13

  val logisticRegressionPath = Paths.get("target", "logistic-regression");

  val outputPath = logisticRegressionPath.resolve("output")

  val inputFile = "/sample_libsvm_data.txt"

  val bigInputFile = logisticRegressionPath.resolve("bigfile.txt")

  var mlModel: LogisticRegressionModel = _

  var sc: SparkContext = _

  var rdd: RDD[(Double, org.apache.spark.ml.linalg.Vector)] = _

  var tempDirPath: Path = _

  def prepareInput() = {
    FileUtils.deleteDirectory(logisticRegressionPath.toFile)
    val text =
      IOUtils.toString(this.getClass.getResourceAsStream(inputFile), StandardCharsets.UTF_8)
    for (i <- 0 until copyCountParam) {
      FileUtils.write(bigInputFile.toFile, text, StandardCharsets.UTF_8, true)
    }
  }

  def loadData() = {
    val num_features = 692
    rdd = sc
      .textFile(bigInputFile.toString)
      .map { line =>
        val parts = line.split(" ")
        val features = new Array[Double](num_features)
        parts.tail.foreach { part =>
          val dimval = part.split(":")
          val index = dimval(0).toInt - 1
          val value = dimval(1).toInt
          features(index) = value
        }
        (parts(0).toDouble, Vectors.dense(features))
      }.cache()
  }

  override def setUpBeforeAll(c: BenchmarkContext): Unit = {
    threadCountParam = c.intParameter("thread_count")
    copyCountParam = c.intParameter("copy_count")

    tempDirPath = c.generateTempDir("log_regression")
    sc = setUpSparkContext(tempDirPath, threadCountParam, "log-regression")
    prepareInput()
    loadData()
    checkCaching(rdd)
  }

  override def run(c: BenchmarkContext): BenchmarkResult = {
    // TODO: Create only once per benchmark?
    val lor = new LogisticRegression()
      .setElasticNetParam(ELASTIC_NET_PARAM)
      .setRegParam(REGULARIZATION_PARAM)
      .setMaxIter(MAX_ITERATIONS)
      .setTol(CONVERGENCE_TOLERANCE)

    val sqlContext = new SQLContext(rdd.context)
    import sqlContext.implicits._
    mlModel = lor.fit(rdd.toDF("label", "features"))

    // TODO: add proper validation
    Validators.dummy(mlModel)
  }

  override def tearDownAfterAll(c: BenchmarkContext): Unit = {
    FileUtils.write(
      outputPath.toFile,
      mlModel.coefficients.toString + "\n",
      StandardCharsets.UTF_8,
      true
    )
    FileUtils.write(outputPath.toFile, mlModel.intercept.toString, StandardCharsets.UTF_8, true)
    tearDownSparkContext(sc)
    c.deleteTempDir(tempDirPath)
  }
}
