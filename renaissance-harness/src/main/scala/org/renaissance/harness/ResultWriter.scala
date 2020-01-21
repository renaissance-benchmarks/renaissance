package org.renaissance.harness

import java.io.File
import java.nio.charset.StandardCharsets

import org.apache.commons.io.FileUtils
import org.renaissance.Benchmark
import org.renaissance.Plugin.BeforeHarnessShutdownListener
import org.renaissance.Plugin.BenchmarkFailureListener
import org.renaissance.Plugin.MeasurementResultListener
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
private abstract class ResultWriter
  extends BeforeHarnessShutdownListener
  with MeasurementResultListener
  with BenchmarkFailureListener {

  private final class FlushOnShutdownThread(val results: ResultWriter) extends Thread {
    override def run(): Unit = {
      results.storeResults(false)
    }
  }

  private final val allResults =
    new mutable.HashMap[String, mutable.Map[String, mutable.ArrayBuffer[Long]]]
  private final val failedBenchmarks = new mutable.ArrayBuffer[String]
  private final val storeHook = new FlushOnShutdownThread(this)

  Runtime.getRuntime.addShutdownHook(storeHook)

  protected def store(normalTermination: Boolean): Unit

  private final def storeResults(normalTermination: Boolean): Unit = this.synchronized {
    // This method is synchronized to ensure we do not overwrite
    // the results when user sends Ctrl-C when store() is already being
    // called (i.e. shutdown hook is still registered but is *almost*
    // no longer needed).
    store(normalTermination)
  }

  final override def beforeHarnessShutdown(): Unit = {
    storeResults(true)
    Runtime.getRuntime.removeShutdownHook(storeHook)
  }

  final override def onMeasurementResult(
    benchmark: String,
    metric: String,
    value: Long
  ): Unit = {
    val benchStorage = allResults.getOrElseUpdate(benchmark, new mutable.HashMap)
    val metricStorage = benchStorage.getOrElseUpdate(metric, new mutable.ArrayBuffer)
    metricStorage += value
  }

  final override def onBenchmarkFailure(benchmark: String): Unit = {
    failedBenchmarks += benchmark
  }

  protected final def getBenchmarks: Iterable[String] = {
    allResults.keys
  }

  protected final def getColumns: Seq[String] = {
    allResults.values.flatMap(_.keys).toSeq.distinct.sorted
  }

  protected final def getResults
    : Iterable[(String, Boolean, Map[String, mutable.ArrayBuffer[Long]], Int)] =
    for {
      benchName <- getBenchmarks
      benchResults = allResults(benchName)
      benchFailed = failedBenchmarks.contains(benchName)
      valueCountMax = benchResults.values.map(_.size).max
    } yield
      (
        benchName,
        benchFailed,
        benchResults.toMap,
        valueCountMax
      )

  protected final def writeToFile(fileName: String, string: String): Unit = {
    FileUtils.write(new File(fileName), string, StandardCharsets.UTF_8, false)
  }

}

private final class CsvWriter(val filename: String) extends ResultWriter {

  override def store(normalTermination: Boolean): Unit = {
    val csv = new StringBuffer

    val columns = getColumns
    formatHeader(columns, csv)
    formatResults(columns, csv)

    writeToFile(filename, csv.toString)
  }

  private def formatHeader(columns: Seq[String], csv: StringBuffer) = {
    // There will always be at least one column after "benchmark".
    csv.append("benchmark,").append(columns.mkString(",")).append("\n")
  }

  private def formatResults(columns: Seq[String], csv: StringBuffer) = {
    for ((benchmark, _, results, repetitions) <- getResults) {
      for (i <- 0 until repetitions) {
        csv.append(benchmark)

        for (c <- columns) {
          val values = results.getOrElse(c, new mutable.ArrayBuffer)
          val score = if (values.isDefinedAt(i)) values(i).toString else "NA"
          csv.append(",").append(score)
        }

        csv.append("\n")
      }
    }
  }

}

private final class JsonWriter(val filename: String) extends ResultWriter {

  private def getEnvironment(termination: String): JsValue = {
    val osInfo = getOsInfo
    val vmInfo = getVmInfo(termination)

    val result = new mutable.HashMap[String, JsValue]
    result.update("os", osInfo.toMap.toJson)
    result.update("vm", vmInfo.toMap.toJson)
    result.toMap.toJson
  }

  private def getOsInfo = {
    val osInfo = new mutable.HashMap[String, JsValue]
    osInfo.update("name", System.getProperty("os.name", "unknown").toJson)
    osInfo.update("arch", System.getProperty("os.arch", "unknown").toJson)
    osInfo.update("version", System.getProperty("os.version", "unknown").toJson)
    osInfo
  }

  private def getVmInfo(termination: String) = {
    val runtimeMxBean = management.ManagementFactory.getRuntimeMXBean
    val vmArgs = runtimeMxBean.getInputArguments

    val vmInfo = new mutable.HashMap[String, JsValue]
    vmInfo.update("name", System.getProperty("java.vm.name", "unknown").toJson)
    vmInfo.update("vm_version", System.getProperty("java.vm.version", "unknown").toJson)
    vmInfo.update("jre_version", System.getProperty("java.version", "unknown").toJson)
    vmInfo.update("args", vmArgs.asScala.toList.toJson)
    vmInfo.update("termination", termination.toJson)
    vmInfo
  }

  private def getMainManifest: java.util.jar.Manifest = {
    val klass = classOf[Benchmark]
    val stream = klass.getResourceAsStream("/META-INF/MANIFEST.MF")
    new java.util.jar.Manifest(stream)
  }

  private def getSuiteInfo: JsValue = {
    val manifestAttrs = getMainManifest.getMainAttributes
    val getManifestAttr = (key: String, defaultValue: String) => {
      val tmp = manifestAttrs.getValue(key)
      if (tmp == null) defaultValue.toJson else tmp.toJson
    }

    def getGitInfo = {
      val git = new mutable.HashMap[String, JsValue]
      git.update("commit_hash", getManifestAttr("Git-Head-Commit", "unknown"))
      git.update("commit_date", getManifestAttr("Git-Head-Commit-Date", "unknown"))
      git.update("dirty", getManifestAttr("Git-Uncommitted-Changes", "true"))
      git
    }

    val result = new mutable.HashMap[String, JsValue]
    result.update("git", getGitInfo.toMap.toJson)
    result.update("name", getManifestAttr("Specification-Title", ""))
    result.update("version", getManifestAttr("Specification-Version", ""))
    result.toMap.toJson
  }

  override def store(normalTermination: Boolean): Unit = {
    val tree = new mutable.HashMap[String, JsValue]
    tree.update("format_version", 4.toJson)
    tree.update("benchmarks", getBenchmarks.toList.toJson)
    tree.update("environment", getEnvironment(if (normalTermination) "normal" else "forced"))
    tree.update("suite", getSuiteInfo)
    tree.update("data", getResultData.toMap.toJson)

    writeToFile(filename, tree.toMap.toJson.prettyPrint)
  }

  private def getResultData = {
    val columns = getColumns

    val dataTree = new mutable.HashMap[String, JsValue]
    for ((benchmark, benchFailed, results, repetitions) <- getResults) {
      val subtree = new mutable.ArrayBuffer[JsValue]
      for (i <- 0 until repetitions) {
        val scores = new mutable.HashMap[String, JsValue]
        for (c <- columns) {
          val values = results.getOrElse(c, new mutable.ArrayBuffer)
          if (values.isDefinedAt(i)) {
            scores.update(c, values(i).toJson)
          }
        }
        subtree += scores.toMap.toJson
      }

      val resultsTree = new mutable.HashMap[String, JsValue]
      resultsTree.update("results", subtree.toList.toJson)
      resultsTree.update("termination", (if (benchFailed) "failure" else "normal").toJson)

      dataTree.update(benchmark, resultsTree.toMap.toJson)
    }

    dataTree
  }

}
