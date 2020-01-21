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

/** Provides common functionality for JSON and CSV result writers.
 *
 * Registers a shutdown hook to avoid losing unsaved results in case
 * the JVM is forcefully terminated.
 *
 * Subclasses are expected to only override the [[store()]] method
 * which actually stores the collected data.
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

  private final val storeHook = new FlushOnShutdownThread(this)

  Runtime.getRuntime.addShutdownHook(storeHook)

  // A result is a map of metric names to a sequence of metric values.
  private final val resultsByBenchmarkName =
    mutable.Map[String, mutable.Map[String, mutable.Buffer[Long]]]()

  private final val failedBenchmarkNames = mutable.Set[String]()

  private final def storeResults(normalTermination: Boolean): Unit = this.synchronized {
    // This method is synchronized to ensure we do not overwrite
    // the results when user sends Ctrl-C when store() is already being
    // called (i.e. shutdown hook is still registered but is *almost*
    // no longer needed).
    if (normalTermination) {
      Runtime.getRuntime.removeShutdownHook(storeHook)
    }

    store(normalTermination)
  }

  final override def beforeHarnessShutdown(): Unit = {
    storeResults(true)
  }

  final override def onMeasurementResult(
    benchmark: String,
    metric: String,
    value: Long
  ): Unit = {
    val metricsByName = resultsByBenchmarkName.getOrElseUpdate(benchmark, mutable.Map())
    val metricValues = metricsByName.getOrElseUpdate(metric, mutable.Buffer())
    metricValues += value
  }

  final override def onBenchmarkFailure(benchmarkName: String): Unit = {
    failedBenchmarkNames += benchmarkName
  }

  protected final def getBenchmarkNames: Iterable[String] = {
    resultsByBenchmarkName.keys
  }

  protected final def getMetricNames: Seq[String] = {
    val metricNames = resultsByBenchmarkName.values.flatMap(_.keys)
    metricNames.toSeq.distinct.sorted
  }

  protected final def getBenchmarkResults
    : Iterable[(String, Boolean, Map[String, mutable.Buffer[Long]], Int)] =
    for {
      benchName <- getBenchmarkNames
      metricsByName = resultsByBenchmarkName(benchName).toMap
      benchFailed = failedBenchmarkNames.contains(benchName)
      repetitionCount = metricsByName.values.map(_.size).max
    } yield (benchName, benchFailed, metricsByName, repetitionCount)

  protected final def writeToFile(fileName: String, string: String): Unit = {
    FileUtils.write(new File(fileName), string, StandardCharsets.UTF_8, false)
  }

  //

  protected def store(normalTermination: Boolean): Unit
}

private final class CsvWriter(val filename: String) extends ResultWriter {

  override def store(normalTermination: Boolean): Unit = {
    val csv = new StringBuffer

    val columns = getMetricNames
    formatHeader(columns, csv)
    formatResults(columns, csv)

    writeToFile(filename, csv.toString)
  }

  private def formatHeader(metricNames: Seq[String], csv: StringBuffer) = {
    // There will always be at least one column after "benchmark".
    csv.append("benchmark,").append(metricNames.mkString(",")).append("\n")
  }

  private def formatResults(metricNames: Seq[String], csv: StringBuffer) = {
    for ((benchmark, _, metricsByName, repetitionCount) <- getBenchmarkResults) {
      for (i <- 0 until repetitionCount) {
        csv.append(benchmark)

        for (metricName <- metricNames) {
          val values = metricsByName.getOrElse(metricName, mutable.Buffer())
          val stringValue = if (values.isDefinedAt(i)) values(i).toString else "NA"
          csv.append(",").append(stringValue)
        }

        csv.append("\n")
      }
    }
  }

}

private final class JsonWriter(val filename: String) extends ResultWriter {

  private def systemPropertyAsJson(name: String) = Option(System.getProperty(name)).toJson

  private def getEnvironment(termination: String) = {
    Map(
      "os" -> getOsInfo.toJson,
      "vm" -> getVmInfo(termination).toJson
    )
  }

  private def getOsInfo = {
    Map(
      "name" -> systemPropertyAsJson("os.name"),
      "arch" -> systemPropertyAsJson("os.arch"),
      "version" -> systemPropertyAsJson("os.version")
    )
  }

  private def getVmInfo(termination: String) = {
    val runtimeMxBean = management.ManagementFactory.getRuntimeMXBean

    Map(
      "name" -> systemPropertyAsJson("java.vm.name"),
      "vm_version" -> systemPropertyAsJson("java.vm.version"),
      "jre_version" -> systemPropertyAsJson("java.version"),
      "args" -> runtimeMxBean.getInputArguments.asScala.toList.toJson,
      "termination" -> termination.toJson
    )
  }

  private def getSuiteInfo = {

    val manifest = {
      val benchClass = classOf[Benchmark]
      val stream = benchClass.getResourceAsStream("/META-INF/MANIFEST.MF")
      new java.util.jar.Manifest(stream)
    }

    def manifestAttrAsJson(key: String, defaultValue: String) = {
      Option(manifest.getMainAttributes.getValue(key)).getOrElse(defaultValue).toJson
    }

    val gitInfo = Map(
      "commit_hash" -> manifestAttrAsJson("Git-Head-Commit", "unknown"),
      "commit_date" -> manifestAttrAsJson("Git-Head-Commit-Date", "unknown"),
      "dirty" -> manifestAttrAsJson("Git-Uncommitted-Changes", "true")
    )

    //

    Map(
      "git" -> gitInfo.toJson,
      "name" -> manifestAttrAsJson("Specification-Title", ""),
      "version" -> manifestAttrAsJson("Specification-Version", "")
    )
  }

  override def store(normalTermination: Boolean): Unit = {
    val result = Map(
      "format_version" -> 4.toJson,
      "benchmarks" -> getBenchmarkNames.toJson,
      "environment" -> getEnvironment(if (normalTermination) "normal" else "forced").toJson,
      "suite" -> getSuiteInfo.toJson,
      "data" -> getResultData.toJson
    )

    writeToFile(filename, result.toJson.prettyPrint)
  }

  private def getResultData = {
    val metricNames = getMetricNames

    val dataTree = mutable.Map[String, JsValue]()
    for ((benchmark, benchFailed, metricsByName, repetitionCount) <- getBenchmarkResults) {
      val subtree = mutable.Buffer[JsValue]()
      for (i <- 0 until repetitionCount) {
        val repetitionValues = mutable.Map[String, JsValue]()
        for (metricName <- metricNames) {
          val values = metricsByName.getOrElse(metricName, mutable.Buffer())
          if (values.isDefinedAt(i)) {
            repetitionValues.update(metricName, values(i).toJson)
          }
        }
        subtree += repetitionValues.toMap.toJson
      }

      val resultsTree = Map(
        "results" -> subtree.toList.toJson,
        "termination" -> (if (benchFailed) "failure" else "normal").toJson
      )

      dataTree.update(benchmark, resultsTree.toJson)
    }

    dataTree.toMap
  }

}
