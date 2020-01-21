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

  private def getMainManifest: java.util.jar.Manifest = {
    val klass = classOf[Benchmark]
    val stream = klass.getResourceAsStream("/META-INF/MANIFEST.MF")
    new java.util.jar.Manifest(stream)
  }

  private def getSuiteInfo = {
    val manifest = getMainManifest

    def manifestAttrAsJson(key: String, defaultValue: String) = {
      Option(manifest.getMainAttributes.getValue(key)).getOrElse(defaultValue).toJson
    }

    def getGitInfo = {
      Map(
        "commit_hash" -> manifestAttrAsJson("Git-Head-Commit", "unknown"),
        "commit_date" -> manifestAttrAsJson("Git-Head-Commit-Date", "unknown"),
        "dirty" -> manifestAttrAsJson("Git-Uncommitted-Changes", "true")
      )
    }

    Map(
      "git" -> getGitInfo.toJson,
      "name" -> manifestAttrAsJson("Specification-Title", ""),
      "version" -> manifestAttrAsJson("Specification-Version", "")
    )
  }

  override def store(normalTermination: Boolean): Unit = {
    val tree = Map(
      "format_version" -> 4.toJson,
      "benchmarks" -> getBenchmarks.toList.toJson,
      "environment" -> getEnvironment(if (normalTermination) "normal" else "forced").toJson,
      "suite" -> getSuiteInfo.toJson,
      "data" -> getResultData.toJson
    )

    writeToFile(filename, tree.toJson.prettyPrint)
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

      val resultsTree = Map(
        "results" -> subtree.toList.toJson,
        "termination" -> (if (benchFailed) "failure" else "normal").toJson
      )

      dataTree.update(benchmark, resultsTree.toJson)
    }

    dataTree.toMap
  }

}
