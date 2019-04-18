package org.renaissance.apache.spark

import java.io.File
import java.nio.charset.StandardCharsets
import java.nio.file.{Path, Paths}
import java.util.zip.ZipInputStream

import org.apache.commons.io.FileUtils
import org.apache.commons.io.IOUtils
import org.apache.spark.SparkContext
import org.apache.spark.SparkConf
import org.apache.spark.ml.Pipeline
import org.apache.spark.ml.PipelineModel
import org.apache.spark.ml.PipelineStage
import org.apache.spark.ml.classification.DecisionTreeClassificationModel
import org.apache.spark.ml.classification.DecisionTreeClassifier
import org.apache.spark.ml.feature.StringIndexer
import org.apache.spark.ml.feature.VectorIndexer
import org.apache.spark.mllib.linalg.Vectors
import org.apache.spark.mllib.regression.LabeledPoint
import org.apache.spark.sql.DataFrame
import org.apache.spark.sql.SQLContext
import org.renaissance.Config
import org.renaissance.License
import org.renaissance.RenaissanceBenchmark

import scala.util.Random

class DecTree extends RenaissanceBenchmark {

  def description = "Runs the Random Forest algorithm from Spark MLlib."

  override def defaultRepetitions = 40

  override def licenses = License.create(License.APACHE2)

  val THREAD_COUNT = Runtime.getRuntime.availableProcessors

  val decisionTreePath = Paths.get("target", "dec-tree")

  val outputPath = decisionTreePath.resolve("output")

  val inputFile = File.separator + "sample_libsvm_data.txt"

  val bigInputFile = decisionTreePath.resolve("bigfile.txt")

  var tempDirPath: Path = null

  var sc: SparkContext = null

  var training: DataFrame = null

  var pipeline: Pipeline = null

  var pipelineModel: PipelineModel = null

  var iteration: Int = 0

  def setUpSpark() = {
    val conf = new SparkConf()
      .setAppName("decision-tree")
      .setMaster(s"local[$THREAD_COUNT]")
      .set("spark.local.dir", tempDirPath.toString)
    sc = new SparkContext(conf)
    sc.setLogLevel("ERROR")
  }

  def prepareAndLoadInput(decisionTreePath: Path, inputFile: String): DataFrame = {
    FileUtils.deleteDirectory(decisionTreePath.toFile)

    val text =
      IOUtils.toString(this.getClass.getResourceAsStream(inputFile), StandardCharsets.UTF_8)
    for (i <- 0 until 100) {
      FileUtils.write(bigInputFile.toFile, text, StandardCharsets.UTF_8, true)
    }

    val sqlContext = new SQLContext(sc)
    return sqlContext.read.format("libsvm").load(bigInputFile.toString)
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
    return new Pipeline().setStages(
      Array[PipelineStage](
        labelIndexer,
        featureIndexer,
        dtc
      )
    )
  }

  override def setUpBeforeAll(c: Config): Unit = {
    tempDirPath = RenaissanceBenchmark.generateTempDir("dec_tree")
    setUpSpark()
    training = prepareAndLoadInput(decisionTreePath, inputFile)
    pipeline = constructPipeline()
  }

  override def runIteration(c: Config): Unit = {
    pipelineModel = pipeline.fit(training)
    val treeModel =
      pipelineModel.stages.last.asInstanceOf[DecisionTreeClassificationModel]
    val thisIterOutputPath = outputPath.resolve(iteration.toString)
    FileUtils.write(
      thisIterOutputPath.toFile,
      treeModel.toDebugString,
      StandardCharsets.UTF_8,
      true
    )
    iteration += 1

  }

  override def tearDownAfterAll(c: Config): Unit = {
    sc.stop()
    RenaissanceBenchmark.deleteTempDir(tempDirPath)
  }
}
