package org.renaissance.apache.spark

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

import java.io.BufferedReader
import java.io.InputStreamReader
import java.nio.file.Files
import java.nio.file.Path
import java.nio.file.StandardOpenOption
import java.util.stream.Collectors

@Name("naive-bayes")
@Group("apache-spark")
@Summary("Runs the multinomial naive Bayes algorithm from the Spark MLlib.")
@Licenses(Array(License.APACHE2))
@Repetitions(30)
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
  defaultValue = "8000",
  summary = "Number of sample data copies to make in the input data."
)
@Configuration(name = "test", settings = Array("copy_count = 5"))
@Configuration(name = "jmh")
final class NaiveBayes extends Benchmark with SparkUtil {

  // TODO: Consolidate benchmark parameters across the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/27

  private val inputResource = "/sample_libsvm_data.txt"

  private val nbSmoothingParam = 1.0

  private var inputLabeledPoints: RDD[LabeledPoint] = _

  private var outputNaiveBayes: NaiveBayesModel = _

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
        new LabeledPoint(parts(0).toDouble, Vectors.dense(features))
      }
      .cache()
  }

  override def setUpBeforeAll(bc: BenchmarkContext): Unit = {
    setUpSparkContext(bc)

    val inputFile = prepareInput(
      inputResource,
      bc.parameter("copy_count").toPositiveInteger,
      bc.scratchDirectory().resolve("input.txt")
    )

    inputLabeledPoints = ensureCached(loadData(inputFile))
  }

  override def run(bc: BenchmarkContext): BenchmarkResult = {
    // Avoid conflict with the Renaissance benchmark class name.
    val bayes = new org.apache.spark.mllib.classification.NaiveBayes()
      .setLambda(nbSmoothingParam)
      .setModelType("multinomial")

    outputNaiveBayes = bayes.run(inputLabeledPoints)

    Validators.compound(
      Validators.simple("pi 0", -0.84397, outputNaiveBayes.pi(0), 0.001),
      Validators.simple("pi 1", -0.56212, outputNaiveBayes.pi(1), 0.001)
    )
  }

  override def tearDownAfterAll(bc: BenchmarkContext): Unit = {
    val outputFile = bc.scratchDirectory().resolve("output.txt")
    dumpResult(outputNaiveBayes, outputFile)

    tearDownSparkContext()
  }

  private def dumpResult(nbm: NaiveBayesModel, outputFile: Path) = {
    val output = new StringBuilder
    output.append(nbm.labels.mkString("labels: ", ", ", "\n"))
    output.append(nbm.pi.mkString("a priori: ", ", ", "\n"))
    output.append(
      nbm.theta.zipWithIndex
        .map({ case (cls, i) => cls.mkString(s"class $i: ", ", ", "") })
        .mkString("thetas:\n", "\n", "")
    )

    // Files.writeString() is only available from Java 11.
    Files.write(outputFile, output.toString.getBytes)
  }

}
