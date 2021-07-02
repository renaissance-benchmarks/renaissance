package org.renaissance.apache.spark

import org.apache.spark.ml.classification.NaiveBayesModel
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

@Name("naive-bayes")
@Group("apache-spark")
@Summary("Runs the multinomial Naive Bayes algorithm from the Spark ML library.")
@Licenses(Array(License.APACHE2))
@Repetitions(30)
@Parameter(
  name = "spark_thread_limit",
  defaultValue = "$cpu.count",
  summary = "Maximum number of threads for the Spark local executor."
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

  private val inputFeatureCount = 692

  private val nbSmoothingParam = 1.0

  private var inputTrainingData: DataFrame = _

  private var outputNaiveBayes: NaiveBayesModel = _

  private def loadData(inputFile: Path, featureCount: Int) = {
    sparkSession.read
      .format("libsvm")
      .option("numFeatures", featureCount)
      .load(inputFile.toString)
  }

  override def setUpBeforeAll(bc: BenchmarkContext): Unit = {
    setUpSparkContext(bc)

    val inputFile = duplicateLinesFromUrl(
      getClass.getResource(inputResource),
      bc.parameter("copy_count").toPositiveInteger,
      bc.scratchDirectory().resolve("input.txt")
    )

    inputTrainingData = ensureCached(loadData(inputFile, inputFeatureCount))
  }

  override def run(bc: BenchmarkContext): BenchmarkResult = {
    // Avoid conflict with the Renaissance benchmark class name.
    val bayes = new org.apache.spark.ml.classification.NaiveBayes()
      .setSmoothing(nbSmoothingParam)
      .setModelType("multinomial")

    outputNaiveBayes = bayes.fit(inputTrainingData)

    Validators.compound(
      Validators.simple("pi 0", -0.84397, outputNaiveBayes.pi(0), 0.001),
      Validators.simple("pi 1", -0.56212, outputNaiveBayes.pi(1), 0.001)
    )
  }

  override def tearDownAfterAll(bc: BenchmarkContext): Unit = {
    if (dumpResultsBeforeTearDown && outputNaiveBayes != null) {
      val outputFile = bc.scratchDirectory().resolve("output.txt")
      dumpResult(outputNaiveBayes, outputFile)
    }

    tearDownSparkContext()
  }

  private def dumpResult(nbm: NaiveBayesModel, outputFile: Path) = {
    val output = new StringBuilder
    output.append(nbm.pi.toArray.mkString("a priori: ", ", ", "\n"))
    output.append(
      nbm.theta.rowIter.zipWithIndex
        .map({ case (cls, i) => cls.toArray.mkString(s"class $i: ", ", ", "") })
        .mkString("thetas:\n", "\n", "")
    )

    // Files.writeString() is only available from Java 11.
    Files.write(outputFile, output.toString.getBytes)
  }

}
