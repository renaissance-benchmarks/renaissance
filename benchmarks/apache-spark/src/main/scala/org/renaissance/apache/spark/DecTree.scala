package org.renaissance.apache.spark

import org.apache.spark.ml.Pipeline
import org.apache.spark.ml.PipelineStage
import org.apache.spark.ml.classification.DecisionTreeClassificationModel
import org.apache.spark.ml.classification.DecisionTreeClassifier
import org.apache.spark.ml.feature.StringIndexer
import org.apache.spark.ml.feature.VectorIndexer
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

@Name("dec-tree")
@Group("apache-spark")
@Summary("Runs the Random Forest algorithm from the Spark ML library.")
@Licenses(Array(License.APACHE2))
@Repetitions(40)
@Parameter(
  name = "spark_thread_limit",
  defaultValue = "6",
  summary = "Maximum number of threads for the Spark local executor."
)
@Parameter(
  name = "copy_count",
  defaultValue = "100",
  summary = "Number of sample data copies to make in the input data."
)
@Configuration(name = "test", settings = Array("copy_count = 5"))
@Configuration(name = "jmh")
final class DecTree extends Benchmark with SparkUtil {

  // TODO: Consolidate benchmark parameters across the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/27

  private val inputResource = "/sample_libsvm_data.txt"

  private val inputFeatureCount = 692

  private var inputTrainingData: DataFrame = _

  private var outputClassificationModel: DecisionTreeClassificationModel = _

  private def loadData(inputFile: Path, featureCount: Int): DataFrame = {
    sparkSession.read
      .format("libsvm")
      .option("numFeatures", featureCount)
      .load(inputFile.toString)
  }

  def constructPipeline(): Pipeline = {
    val labelIndexer = new StringIndexer()
      .setInputCol("label")
      .setOutputCol("indexedLabel")

    val featureIndexer = new VectorIndexer()
      .setInputCol("features")
      .setOutputCol("indexedFeatures")
      .setMaxCategories(10)

    val dtc = new DecisionTreeClassifier()
      .setFeaturesCol("indexedFeatures")
      .setLabelCol("indexedLabel")
      .setMaxDepth(5)
      .setMaxBins(32)
      .setMinInstancesPerNode(1)
      .setMinInfoGain(0.0)
      .setCacheNodeIds(false)
      .setCheckpointInterval(10)
      .setSeed(159147643)

    new Pipeline().setStages(
      Array[PipelineStage](
        labelIndexer,
        featureIndexer,
        dtc
      )
    )
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
    // Always create a new pipeline to avoid (potential) caching.
    val outputPipelineModel = constructPipeline().fit(inputTrainingData)
    val lastStage = outputPipelineModel.stages.last
    outputClassificationModel = lastStage.asInstanceOf[DecisionTreeClassificationModel]

    // TODO: add more in-depth validation
    Validators.compound(
      Validators.simple("tree depth", 2, outputClassificationModel.depth),
      Validators.simple("node count", 5, outputClassificationModel.numNodes),
      Validators.simple("class count", 2, outputClassificationModel.numClasses),
      Validators.simple("feature count", 692, outputClassificationModel.numFeatures)
    )
  }

  override def tearDownAfterAll(bc: BenchmarkContext): Unit = {
    if (dumpResultsBeforeTearDown && outputClassificationModel != null) {
      val outputFile = bc.scratchDirectory().resolve("output.txt")
      dumpResult(outputClassificationModel, outputFile)
    }

    tearDownSparkContext()
  }

  private def dumpResult(dtcm: DecisionTreeClassificationModel, outputFile: Path) = {
    // Create a header with information about model properties and attach to
    // it a debug dump of the underlying tree (without the first line containing UID).
    val header = Seq(
      s"depth=${dtcm.depth}, numNodes=${dtcm.numNodes}, " +
        s"numClasses=${dtcm.numClasses}, numFeatures=${dtcm.numFeatures}"
    )
    val body = dtcm.toDebugString.linesIterator.toSeq.tail
    val dtcmDump = (header ++ body).mkString("\n")

    // Files.writeString() is only available from Java 11.
    Files.write(outputFile, dtcmDump.getBytes)
  }

}
