package org.renaissance.apache.spark

import java.nio.charset.StandardCharsets
import java.nio.file.Paths

import org.apache.commons.io.FileUtils
import org.apache.commons.io.IOUtils
import org.apache.spark.SparkContext
import org.apache.spark.mllib.classification.NaiveBayesModel
import org.apache.spark.mllib.linalg.Vectors
import org.apache.spark.mllib.regression.LabeledPoint
import org.apache.spark.rdd.RDD
import org.renaissance.Benchmark
import org.renaissance.Benchmark._
import org.renaissance.BenchmarkContext
import org.renaissance.BenchmarkResult
import org.renaissance.BenchmarkResult.Validators
import org.renaissance.License

@Name("naive-bayes")
@Group("apache-spark")
@Summary("Runs the multinomial naive Bayes algorithm from the Spark MLlib.")
@Licenses(Array(License.APACHE2))
@Repetitions(30)
class NaiveBayes extends Benchmark with SparkUtil {

  // TODO: Consolidate benchmark parameters across the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/27

  val SMOOTHING = 1.0

  val THREAD_COUNT = Runtime.getRuntime.availableProcessors

  val naiveBayesPath = Paths.get("target", "naive-bayes")

  val outputPath = naiveBayesPath.resolve("output")

  val inputFile = "/sample_libsvm_data.txt"

  val bigInputFile = naiveBayesPath.resolve("bigfile.txt")

  var sc: SparkContext = null

  var data: RDD[LabeledPoint] = null

  var bayesModel: NaiveBayesModel = null

  def prepareInput() = {
    FileUtils.deleteDirectory(naiveBayesPath.toFile)
    val text =
      IOUtils.toString(this.getClass.getResourceAsStream(inputFile), StandardCharsets.UTF_8)
    for (i <- 0 until 8000) {
      FileUtils.write(bigInputFile.toFile, text, true)
    }
  }

  def loadData() = {
    val num_features = 692
    data = sc
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
        new LabeledPoint(parts(0).toDouble, Vectors.dense(features))
      }
      .cache()
  }

  override def setUpBeforeAll(c: BenchmarkContext): Unit = {
    val tempDirPath = c.scratchDirectory()
    sc = setUpSparkContext(tempDirPath, THREAD_COUNT)
    prepareInput()
    loadData()
    ensureCaching(data)
  }

  override def tearDownAfterAll(c: BenchmarkContext): Unit = {
    // Dump output.
    FileUtils.write(
      outputPath.toFile,
      bayesModel.labels.mkString("labels: ", ", ", "\n"),
      StandardCharsets.UTF_8,
      true
    )

    FileUtils.write(
      outputPath.toFile,
      bayesModel.pi.mkString("a priori: ", ", ", "\n"),
      StandardCharsets.UTF_8,
      true
    )

    FileUtils.write(
      outputPath.toFile,
      bayesModel.theta.zipWithIndex
        .map {
          case (cls, i) =>
            cls.mkString(s"class $i: ", ", ", "")
        }
        .mkString("thetas:\n", "\n", ""),
      StandardCharsets.UTF_8,
      true
    )

    tearDownSparkContext(sc)
  }

  override def run(c: BenchmarkContext): BenchmarkResult = {
    // Using full package name to avoid conflicting with the renaissance benchmark class name.
    val bayes = new org.apache.spark.mllib.classification.NaiveBayes()
      .setLambda(SMOOTHING)
      .setModelType("multinomial")
    bayesModel = bayes.run(data)

    Validators.compound(
      Validators.simple("pi 0", -0.84397, bayesModel.pi(0), 0.001),
      Validators.simple("pi 1", -0.56212, bayesModel.pi(1), 0.001)
    )
  }
}
