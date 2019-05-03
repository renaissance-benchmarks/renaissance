package org.renaissance.apache.spark

import java.nio.charset.StandardCharsets
import java.nio.file.{Path, Paths}

import org.apache.commons.io.FileUtils
import org.apache.commons.io.IOUtils
import org.apache.spark.ml.classification.{LogisticRegression, LogisticRegressionModel}
import org.apache.spark.ml.linalg.Vectors
import org.apache.spark.rdd.RDD
import org.apache.spark.sql._
import org.apache.spark.{SparkConf, SparkContext}
import org.renaissance.{Config, License, RenaissanceBenchmark}

class LogRegression extends RenaissanceBenchmark with SparkUtil {

  def description = "Runs the logistic regression workload from the Spark MLlib."

  override def defaultRepetitions = 20

  override def licenses(): Array[License] = License.create(License.APACHE2)

  val REGULARIZATION_PARAM = 0.1

  val MAX_ITERATIONS = 20

  val ELASTIC_NET_PARAM = 0.0

  val CONVERGENCE_TOLERANCE = 0.0

  // TODO: Consolidate benchmark parameters across the suite.
  //  See: https://github.com/D-iii-S/renaissance-benchmarks/issues/27

  val THREAD_COUNT = Runtime.getRuntime.availableProcessors

  val logisticRegressionPath = Paths.get("target", "logistic-regression");

  val outputPath = logisticRegressionPath.resolve("output")

  val inputFile = "/sample_libsvm_data.txt"

  val bigInputFile = logisticRegressionPath.resolve("bigfile.txt")

  var mlModel: LogisticRegressionModel = null

  var sc: SparkContext = null

  var rdd: RDD[(Double, org.apache.spark.ml.linalg.Vector)] = null

  var tempDirPath: Path = null

  def prepareInput() = {
    FileUtils.deleteDirectory(logisticRegressionPath.toFile)
    val text =
      IOUtils.toString(this.getClass.getResourceAsStream(inputFile), StandardCharsets.UTF_8)
    for (i <- 0 until 400) {
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
      }
  }

  override def setUpBeforeAll(c: Config): Unit = {
    tempDirPath = RenaissanceBenchmark.generateTempDir("log_regression")
    sc = setUpSparkContext(tempDirPath, THREAD_COUNT)
    prepareInput()
    loadData()
  }

  protected override def runIteration(config: Config): Unit = {
    val lor = new LogisticRegression()
      .setElasticNetParam(ELASTIC_NET_PARAM)
      .setRegParam(REGULARIZATION_PARAM)
      .setMaxIter(MAX_ITERATIONS)
      .setTol(CONVERGENCE_TOLERANCE)
    val sqlContext = new SQLContext(rdd.context)
    import sqlContext.implicits._
    mlModel = lor.fit(rdd.toDF("label", "features"))
  }

  override def tearDownAfterAll(c: Config): Unit = {
    FileUtils.write(outputPath.toFile, mlModel.coefficients.toString + "\n", true)
    FileUtils.write(outputPath.toFile, mlModel.intercept.toString, true)
    tearDownSparkContext(sc)
    RenaissanceBenchmark.deleteTempDir(tempDirPath)
  }
}
