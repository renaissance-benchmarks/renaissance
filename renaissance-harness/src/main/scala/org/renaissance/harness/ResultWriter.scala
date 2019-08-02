package org.renaissance.harness

import java.io.File
import java.nio.charset.StandardCharsets

import org.apache.commons.io.FileUtils
import org.renaissance.Benchmark
import org.renaissance.Plugin.BenchmarkFailureListener
import org.renaissance.Plugin.BenchmarkResultListener
import org.renaissance.Plugin.HarnessShutdownListener
import spray.json._
import spray.json.DefaultJsonProtocol._

import scala.collection.JavaConverters._
import scala.collection.mutable

/** Common functionality for JSON and CSV results writers.
 *
 * This class takes care of registering a shutdown hook so that the results
 * are not lost when JVM is forcefully terminated.
 *
 * Descendants are expected to override only the store() method that
 * actually stores the collected data.
 */
abstract class ResultWriter
  extends HarnessShutdownListener
  with BenchmarkResultListener
  with BenchmarkFailureListener {

  class FlushOnShutdownThread(val results: ResultWriter) extends Thread {
    override def run(): Unit = {
      results.storeResults(false)
    }
  }

  val allResults = new mutable.HashMap[String, mutable.Map[String, mutable.ArrayBuffer[Long]]]
  val failedBenchmarks = new mutable.ArrayBuffer[String]
  val storeHook = new FlushOnShutdownThread(this)

  Runtime.getRuntime.addShutdownHook(storeHook)

  protected def store(normalTermination: Boolean): Unit

  def storeResults(normalTermination: Boolean): Unit = this.synchronized {
    // This method is synchronized to ensure we do not overwrite
    // the results when user sends Ctrl-C when store() is already being
    // called (i.e. shutdown hook is still registered but is *almost*
    // no longer needed).
    store(normalTermination)
  }

  override def beforeHarnessShutdown(): Unit = {
    storeResults(true)
    Runtime.getRuntime.removeShutdownHook(storeHook)
  }

  override def onBenchmarkResult(benchmark: String, metric: String, value: Long): Unit = {
    val benchStorage = allResults.getOrElse(benchmark, new mutable.HashMap)
    allResults.update(benchmark, benchStorage)
    val metricStorage = benchStorage.getOrElse(metric, new mutable.ArrayBuffer)
    benchStorage.update(metric, metricStorage)
    metricStorage += value
  }

  override def onBenchmarkFailure(benchmark: String): Unit = {
    failedBenchmarks += benchmark
  }

  def getBenchmarks: Iterable[String] = {
    allResults.keys
  }

  def getColumns: Seq[String] = {
    allResults.values.flatMap(_.keys).toSeq.distinct.sorted
  }

  def getResults
    : Iterable[(String, Boolean, Map[String, mutable.ArrayBuffer[Long]], Iterable[Int])] =
    for {
      benchName <- getBenchmarks
      benchResults = allResults(benchName)
      maxIndex = benchResults.values.map(_.size).max - 1
    } yield
      (
        benchName,
        !failedBenchmarks.contains(benchName),
        benchResults.toMap,
        0 to maxIndex
      )
}

class CsvWriter(val filename: String) extends ResultWriter {

  def store(normalTermination: Boolean): Unit = {
    val csv = new StringBuffer
    csv.append("benchmark")
    val columns = new mutable.ArrayBuffer[String]
    for (c <- getColumns) {
      columns += c
      csv.append(",").append(c)
    }
    csv.append("\n")

    for ((benchmark, goodRuns, results, repetitions) <- getResults) {
      for (i <- repetitions) {
        val line = new StringBuffer
        line.append(benchmark)
        for (c <- columns) {
          val values = results.getOrElse(c, new mutable.ArrayBuffer)
          val score = if (i < values.size) values(i).toString else "NA"
          line.append(",").append(score.toString)
        }
        csv.append(line).append("\n")
      }
    }

    FileUtils.write(
      new File(filename),
      csv.toString,
      StandardCharsets.UTF_8,
      false
    )
  }
}

class JsonWriter(val filename: String) extends ResultWriter {

  def getEnvironment(termination: String): JsValue = {
    val result = new mutable.HashMap[String, JsValue]

    val osInfo = new mutable.HashMap[String, JsValue]
    osInfo.update("name", System.getProperty("os.name", "unknown").toJson)
    osInfo.update("arch", System.getProperty("os.arch", "unknown").toJson)
    osInfo.update("version", System.getProperty("os.version", "unknown").toJson)
    result.update("os", osInfo.toMap.toJson)

    val runtimeMxBean = management.ManagementFactory.getRuntimeMXBean
    val vmArgs = runtimeMxBean.getInputArguments

    val vmInfo = new mutable.HashMap[String, JsValue]
    vmInfo.update("name", System.getProperty("java.vm.name", "unknown").toJson)
    vmInfo.update("vm_version", System.getProperty("java.vm.version", "unknown").toJson)
    vmInfo.update("jre_version", System.getProperty("java.version", "unknown").toJson)
    vmInfo.update("args", vmArgs.asScala.toList.toJson)
    vmInfo.update("termination", termination.toJson)
    result.update("vm", vmInfo.toMap.toJson)

    result.toMap.toJson
  }

  def getMainManifest: java.util.jar.Manifest = {
    val klass = classOf[Benchmark]
    val stream = klass.getResourceAsStream("/META-INF/MANIFEST.MF")
    new java.util.jar.Manifest(stream)
  }

  def getSuiteInfo: JsValue = {
    val result = new mutable.HashMap[String, JsValue]

    val manifestAttrs = getMainManifest.getMainAttributes
    val getManifestAttr = (key: String, defaultValue: String) => {
      val tmp = manifestAttrs.getValue(key)
      if (tmp == null) defaultValue.toJson else tmp.toJson
    }

    val git = new mutable.HashMap[String, JsValue]
    git.update("commit_hash", getManifestAttr("Git-Head-Commit", "unknown"))
    git.update("commit_date", getManifestAttr("Git-Head-Commit-Date", "unknown"))
    git.update("dirty", getManifestAttr("Git-Uncommitted-Changes", "true"))

    result.update("git", git.toMap.toJson)
    result.update("name", getManifestAttr("Specification-Title", ""))
    result.update("version", getManifestAttr("Specification-Version", ""))

    result.toMap.toJson
  }

  def store(normalTermination: Boolean): Unit = {
    val columns = getColumns

    val tree = new mutable.HashMap[String, JsValue]
    tree.update("format_version", 4.toJson)
    tree.update("benchmarks", getBenchmarks.toList.toJson)
    tree.update("environment", getEnvironment(if (normalTermination) "normal" else "forced"))
    tree.update("suite", getSuiteInfo)

    val dataTree = new mutable.HashMap[String, JsValue]
    for ((benchmark, goodRuns, results, repetitions) <- getResults) {
      val subtree = new mutable.ArrayBuffer[JsValue]
      for (i <- repetitions) {
        val scores = new mutable.HashMap[String, JsValue]
        for (c <- columns) {
          val values = results.getOrElse(c, new mutable.ArrayBuffer)
          if (i < values.size) {
            scores.update(c, values(i).toJson)
          }
        }
        subtree += scores.toMap.toJson
      }
      val resultsTree = new mutable.HashMap[String, JsValue]
      resultsTree.update("results", subtree.toList.toJson)
      resultsTree.update("termination", (if (goodRuns) "normal" else "failure").toJson)
      dataTree.update(benchmark, resultsTree.toMap.toJson)
    }

    tree.update("data", dataTree.toMap.toJson)

    FileUtils.write(
      new File(filename),
      tree.toMap.toJson.prettyPrint,
      java.nio.charset.StandardCharsets.UTF_8,
      false
    )
  }
}
