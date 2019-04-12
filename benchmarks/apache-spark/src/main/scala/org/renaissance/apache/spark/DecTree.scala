package org.renaissance.apache.spark

import java.io.File
import java.nio.charset.StandardCharsets
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

  //override def defaultRepetitions = ?? //Currently not set. Shall we keep the default value?

  override def licenses = License.create(License.APACHE2)

  val THREAD_COUNT = Runtime.getRuntime.availableProcessors

  val decisionTreePath = "target/dec-tree"

  val outputPath = decisionTreePath + "/output"

  val inputFile = "/sample_libsvm_data.txt"

  val bigInputFile = decisionTreePath + "/bigfile.txt"

  var sc: SparkContext = null

  var training: DataFrame = null

  var pipeline: Pipeline = null

  var pipelineModel: PipelineModel = null

  override def setUpBeforeAll(c: Config): Unit = {
    val conf = new SparkConf()
      .setAppName("decision-tree")
      .setMaster(s"local[$THREAD_COUNT]")
      .set("spark.local.dir", "_tmp")
    sc = new SparkContext(conf)
    sc.setLogLevel("ERROR")

    // Prepare input.
    FileUtils.deleteDirectory(new File(decisionTreePath))
    val text = IOUtils.toString(this.getClass.getResourceAsStream(inputFile), StandardCharsets.UTF_8)
    for (i <- 0 until 100) {
      FileUtils.write(new File(bigInputFile), text, StandardCharsets.UTF_8, true)
    }

    // Load data.
    val sqlContext = new SQLContext(sc)
    training = sqlContext.read.format("libsvm").load(bigInputFile)

    // Run decision tree algorithm.
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
    pipeline = new Pipeline().setStages(Array[PipelineStage](
      labelIndexer,
      featureIndexer,
      dtc
    ))
  }


  override def runIteration(c: Config): Unit = {
    pipelineModel = pipeline.fit(training)
  }

  override def tearDownAfterAll(c: Config): Unit = {
    // Dump output.
    val treeModel =
      pipelineModel.stages.last.asInstanceOf[DecisionTreeClassificationModel]
    FileUtils.write(new File(outputPath), treeModel.toDebugString, StandardCharsets.UTF_8, true)

    sc.stop()
  }


}
