package org.renaissance.apache.spark

import java.io._
import java.nio.charset.StandardCharsets
import java.util.zip.ZipInputStream

import org.apache.commons.io.{FileUtils, IOUtils}
import org.apache.spark.{SparkConf, SparkContext}
import org.apache.spark.ml.classification.{LogisticRegression, LogisticRegressionModel}
import org.apache.spark.ml.linalg.Vectors
import org.apache.spark.rdd.RDD
import org.apache.spark.sql._
import org.renaissance.{Config, License, RenaissanceBenchmark}


class LogRegression extends RenaissanceBenchmark {

  def description = "Runs the logistic regression workload from mllib."

  override def defaultRepetitions = 20

  override def licenses(): Array[License] = License.create(License.APACHE2)

  val REGULARIZATION_PARAM = 0.1

  val MAX_ITERATIONS = 20

  val ELASTIC_NET_PARAM = 0.0

  val CONVERGENCE_TOLERANCE = 0.0

  val THREAD_COUNT = Runtime.getRuntime.availableProcessors

  val logisticRegressionPath = "target/logistic-regression"

  val outputPath = logisticRegressionPath + "/output"

  val inputFile = "/sample_libsvm_data.txt.zip"

  val bigInputFile = logisticRegressionPath + "/bigfile.txt"

  var mlModel: LogisticRegressionModel = null

  var sc: SparkContext = null

  var rdd: RDD[(Double, org.apache.spark.ml.linalg.Vector)] = null


  override def setUpBeforeAll(c: Config): Unit = {

    val conf = new SparkConf().setAppName("logistic-regression")
      .setMaster(s"local[$THREAD_COUNT]")
      .set("spark.local.dir", "_tmp")
    sc = new SparkContext(conf)
    sc.setLogLevel("ERROR")

    // Prepare input.
    FileUtils.deleteDirectory(new File(logisticRegressionPath))
    val zis = new ZipInputStream(this.getClass.getResourceAsStream(inputFile))
    zis.getNextEntry()
    val text = IOUtils.toString(zis, StandardCharsets.UTF_8)
    for (i <- 0 until 400) {
      FileUtils.write(new File(bigInputFile), text, true)
    }

    // Load data.
    rdd = sc.textFile(bigInputFile)
      .map { line =>
        val parts = line.split(" ")
        val features = new Array[Double](692)
        parts.tail.foreach { part =>
          val dimval = part.split(":")
          val index = dimval(0).toInt - 1
          val value = dimval(1).toInt
          features(index) = value
        }
        (parts(0).toDouble, Vectors.dense(features))
      }
  }

  override def tearDownAfterAll(c: Config): Unit = {
    // Dump output.
    FileUtils.write(new File(outputPath), mlModel.coefficients.toString + "\n", true)
    FileUtils.write(new File(outputPath), mlModel.intercept.toString, true)
    sc.stop()
    try {
      FileUtils.deleteDirectory(new java.io.File("_tmp"))
    } catch {
      case t: Throwable =>
        println("Error removing temp directory ! " + t.getMessage)
    }
  }

  override protected def runIteration(config: Config): Unit = {
    val lor = new LogisticRegression()
      .setElasticNetParam(ELASTIC_NET_PARAM)
      .setRegParam(REGULARIZATION_PARAM)
      .setMaxIter(MAX_ITERATIONS)
      .setTol(CONVERGENCE_TOLERANCE)
    val sqlContext = new SQLContext(rdd.context)
    import sqlContext.implicits._
    mlModel = lor.fit(rdd.toDF("label", "features"))
  }
}
