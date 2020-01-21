package org.renaissance.harness

import java.io.File
import java.lang.management.MemoryUsage
import java.nio.charset.StandardCharsets
import java.text.SimpleDateFormat
import java.util.Date
import java.util.TimeZone

import com.sun.management.UnixOperatingSystemMXBean
import org.apache.commons.io.FileUtils
import org.renaissance.Benchmark
import org.renaissance.Plugin.BeforeHarnessShutdownListener
import org.renaissance.Plugin.BenchmarkFailureListener
import org.renaissance.Plugin.MeasurementResultListener
import spray.json.DefaultJsonProtocol._
import spray.json._

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

  private def formatHeader(metricNames: Seq[String], csv: StringBuffer): Unit = {
    // There will always be at least one column after "benchmark".
    csv.append("benchmark,").append(metricNames.mkString(",")).append(",vm_start_unix_ms\n")
  }

  private def formatResults(metricNames: Seq[String], csv: StringBuffer): Unit = {
    val vmStartTime = management.ManagementFactory.getRuntimeMXBean.getStartTime
    for ((benchmark, _, metricsByName, repetitionCount) <- getBenchmarkResults) {
      for (i <- 0 until repetitionCount) {
        csv.append(benchmark)

        for (metricName <- metricNames) {
          val values = metricsByName.get(metricName)
          val stringValue = values.map(values => values(i).toString).getOrElse("NA")
          csv.append(",").append(stringValue)
        }

        csv.append(",").append(vmStartTime).append("\n")
      }
    }
  }

}

private final class JsonWriter(val filename: String) extends ResultWriter {

  private def systemPropertyAsJson(name: String) = Option(System.getProperty(name)).toJson

  private def pathsAsJson(pathSpec: String) = pathSpec.split(File.pathSeparator).toJson

  private def getEnvironment(normalTermination: Boolean) = {
    Map(
      "os" -> getOsInfo,
      "vm" -> getVmInfo(normalTermination),
      "jre" -> getJreInfo
    )
  }

  private def getOsInfo = {
    val os = management.ManagementFactory.getOperatingSystemMXBean

    val result = mutable.Map(
      "name" -> os.getName.toJson,
      "arch" -> os.getArch.toJson,
      "version" -> os.getVersion.toJson,
      "available_processors" -> os.getAvailableProcessors.toJson
    )

    os match {
      case unixOs: UnixOperatingSystemMXBean =>
        result ++= Map(
          "phys_mem_total" -> unixOs.getTotalPhysicalMemorySize.toJson,
          "phys_mem_free" -> unixOs.getFreePhysicalMemorySize.toJson,
          "virt_mem_committed" -> unixOs.getCommittedVirtualMemorySize.toJson,
          "swap_space_total" -> unixOs.getTotalSwapSpaceSize.toJson,
          "swap_space_free" -> unixOs.getFreeSwapSpaceSize.toJson,
          "max_fd_count" -> unixOs.getMaxFileDescriptorCount.toJson,
          "open_fd_count" -> unixOs.getOpenFileDescriptorCount.toJson
        )
    }

    result.toMap
  }

  private def getVmInfo(normalTermination: Boolean) = {
    val runtimeMxBean = management.ManagementFactory.getRuntimeMXBean

    Map(
      "name" -> runtimeMxBean.getVmName.toJson,
      "vendor" -> runtimeMxBean.getVmVendor.toJson,
      "version" -> runtimeMxBean.getVmVersion.toJson,
      "spec_name" -> runtimeMxBean.getSpecName.toJson,
      "spec_vendor" -> runtimeMxBean.getSpecVendor.toJson,
      "spec_version" -> runtimeMxBean.getSpecVersion.toJson,
      "mode" -> systemPropertyAsJson("java.vm.info"),
      "args" -> runtimeMxBean.getInputArguments.asScala.toList.toJson,
      "termination" -> (if (normalTermination) "normal" else "forced").toJson,
      "start_unix_ms" -> runtimeMxBean.getStartTime.toJson,
      "start_iso" -> unixTimeAsIso(runtimeMxBean.getStartTime).toJson,
      "uptime_ms" -> runtimeMxBean.getUptime.toJson,
      "collectors" -> getCollectorInfo.toJson,
      "compiler" -> getCompilationInfo.toJson,
      "classloading" -> getClassLoadingInfo.toJson,
      "memory" -> getMemoryInfo.toJson,
      "pools" -> getMemoryPoolInfo.toJson,
      "threads" -> getThreadInfo.toJson
    )
  }

  private def getJreInfo = {
    val runtimeMxBean = management.ManagementFactory.getRuntimeMXBean

    Map(
      "name" -> systemPropertyAsJson("java.runtime.name"),
      "version" -> systemPropertyAsJson("java.runtime.version"),
      "java_vendor" -> systemPropertyAsJson("java.vendor"),
      "java_version" -> systemPropertyAsJson("java.version"),
      "spec_name" -> systemPropertyAsJson("java.specification.name"),
      "spec_vendor" -> systemPropertyAsJson("java.specification.vendor"),
      "spec_version" -> systemPropertyAsJson("java.specification.version"),
      "home" -> systemPropertyAsJson("java.home"),
      "library_path" -> pathsAsJson(runtimeMxBean.getLibraryPath),
      "boot_class_path" -> pathsAsJson(runtimeMxBean.getBootClassPath),
      "class_path" -> pathsAsJson(runtimeMxBean.getClassPath)
    )
  }

  private def unixTimeAsIso(unixTime: Long) = {
    val formatter = new SimpleDateFormat("yyyy-MM-dd'T'HH:mm:ss.SSS'Z'")
    formatter.setTimeZone(TimeZone.getTimeZone("UTC"))
    formatter.format(new Date(unixTime))
  }

  private def getMemoryUsageInfo(usage: MemoryUsage) = {
    Map(
      "init" -> usage.getInit.toJson,
      "used" -> usage.getUsed.toJson,
      "committed" -> usage.getCommitted.toJson,
      "max" -> usage.getMax.toJson
    )
  }

  private def getMemoryInfo = {
    val info = management.ManagementFactory.getMemoryMXBean

    Map(
      "heap_usage" -> getMemoryUsageInfo(info.getHeapMemoryUsage).toJson,
      "nonheap_usage" -> getMemoryUsageInfo(info.getNonHeapMemoryUsage).toJson,
      "pending_finalization_count" -> info.getObjectPendingFinalizationCount.toJson
    )
  }

  private def getMemoryPoolInfo = {
    val pools = management.ManagementFactory.getMemoryPoolMXBeans.asScala

    pools
      .map(pool => {
        Map(
          "name" -> pool.getName.toJson,
          "type" -> pool.getType.name().toJson,
          "usage" -> getMemoryUsageInfo(pool.getUsage).toJson,
          "peak_usage" -> getMemoryUsageInfo(pool.getPeakUsage).toJson
        )
      })
      .toList
  }

  private def getCollectorInfo = {
    val collectors = management.ManagementFactory.getGarbageCollectorMXBeans.asScala

    collectors
      .map(gc => {
        Map(
          "name" -> gc.getName.toJson,
          "collection_count" -> gc.getCollectionCount.toJson,
          "collection_time_ms" -> gc.getCollectionTime.toJson
        )
      })
      .toList
  }

  private def getCompilationInfo = {
    val info = management.ManagementFactory.getCompilationMXBean
    if (info != null) {
      val result = mutable.Buffer(
        "name" -> info.getName.toJson
      )

      if (info.isCompilationTimeMonitoringSupported) {
        result += ("compilation_time_ms" -> info.getTotalCompilationTime.toJson)
      }

      Option(result.toMap)
    } else {
      // Compilation MX Bean is not available in interpreted mode.
      Option.empty
    }
  }

  private def getClassLoadingInfo = {
    val info = management.ManagementFactory.getClassLoadingMXBean

    Map(
      "class_count" -> info.getLoadedClassCount.toJson,
      "classes_total" -> info.getTotalLoadedClassCount.toJson
    )
  }

  private def getThreadInfo = {
    val info = management.ManagementFactory.getThreadMXBean

    Map(
      "thread_count" -> info.getThreadCount.toJson,
      "thread_count_max" -> info.getPeakThreadCount.toJson,
      "daemon_thread_count" -> info.getDaemonThreadCount.toJson,
      "threads_total" -> info.getTotalStartedThreadCount.toJson
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
      "format_version" -> 5.toJson,
      "benchmarks" -> getBenchmarkNames.toJson,
      "environment" -> getEnvironment(normalTermination).toJson,
      "suite" -> getSuiteInfo.toJson,
      "data" -> getResultData.toJson
    )

    writeToFile(filename, result.toJson.prettyPrint)
  }

  private def getResultData = {
    val metricNames = getMetricNames

    val dataTree = mutable.Map[String, JsValue]()
    for ((benchmark, benchFailed, metricsByName, repetitionCount) <- getBenchmarkResults) {
      // Collect (name -> value) tuples for metrics into a map for each repetition.
      val repetitions = (0 until repetitionCount).map(
        i =>
          metricNames
            .map(name => metricsByName.get(name).map(values => (name -> values(i).toJson)))
            .flatten
            .toMap
      )

      val benchmarkTree = Map(
        "results" -> repetitions.toJson,
        "termination" -> (if (benchFailed) "failure" else "normal").toJson
      )

      dataTree.update(benchmark, benchmarkTree.toJson)
    }

    dataTree.toMap
  }

}
