package org.renaissance.harness

import com.sun.management.UnixOperatingSystemMXBean
import org.renaissance.Benchmark
import org.renaissance.Plugin.BeforeHarnessShutdownListener
import org.renaissance.Plugin.BenchmarkFailureListener
import org.renaissance.Plugin.MeasurementResultListener
import spray.json.DefaultJsonProtocol._
import spray.json._

import java.io.File
import java.lang.management.MemoryUsage
import java.nio.file.Files
import java.nio.file.Path
import java.nio.file.Paths
import java.nio.file.StandardOpenOption
import java.text.SimpleDateFormat
import java.util.Date
import java.util.TimeZone
import scala.util.Try
import scala.collection.mutable
import scala.jdk.CollectionConverters._

/**
 * Provides common functionality for JSON and CSV result writers.
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

  private final def storeResults(normalTermination: Boolean): Unit =
    this.synchronized {
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

  protected final def writeToFile(file: Path, string: String): Unit = {
    if (file.equals(Paths.get("-"))) {
      println(string)
    } else {
      val writer = Files.newBufferedWriter(
        file,
        StandardOpenOption.CREATE,
        StandardOpenOption.TRUNCATE_EXISTING
      )
      try {
        writer.append(string)
      } finally {
        writer.close()
      }
    }
  }

  //

  protected def store(normalTermination: Boolean): Unit
}

private final class CsvWriter(val csvFile: Path) extends ResultWriter {

  override def store(normalTermination: Boolean): Unit = {
    val csv = new StringBuilder

    val columns = getMetricNames
    formatHeader(columns, csv)
    formatResults(columns, csv)

    writeToFile(csvFile, csv.toString)
  }

  private def formatHeader(metricNames: Seq[String], csv: StringBuilder): Unit = {
    // There will always be at least one column after "benchmark".
    csv.append("benchmark,").append(metricNames.mkString(",")).append(",vm_start_unix_ms\n")
  }

  private def formatResults(metricNames: Seq[String], csv: StringBuilder): Unit = {
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

private final class JsonWriter(val jsonFile: Path) extends ResultWriter {

  private def systemPropertyAsJson(name: String) = Option(System.getProperty(name)).toJson

  private def pathsAsJson(pathSpec: String) = {
    if (pathSpec != null) {
      pathSpec.split(File.pathSeparator).toJson
    } else {
      Array.empty[String].toJson
    }
  }

  private def getEnvironment(normalTermination: Boolean) = {
    Map(
      "os" -> getOsInfo,
      "vm" -> getVmInfo(normalTermination),
      "jre" -> getJreInfo
    )
  }

  private def getOsInfo = {
    val os = management.ManagementFactory.getOperatingSystemMXBean

    val result = mutable.Buffer(
      "name" -> os.getName.toJson,
      "arch" -> os.getArch.toJson,
      "version" -> os.getVersion.toJson,
      "available_processors" -> os.getAvailableProcessors.toJson
    )

    os match {
      case unixOs: UnixOperatingSystemMXBean =>
        // Gag possible exceptions.
        result ++= Seq(
          "phys_mem_total" -> Try(unixOs.getTotalPhysicalMemorySize).toOption.toJson,
          "phys_mem_free" -> Try(unixOs.getFreePhysicalMemorySize).toOption.toJson,
          "virt_mem_committed" -> Try(unixOs.getCommittedVirtualMemorySize).toOption.toJson,
          "swap_space_total" -> Try(unixOs.getTotalSwapSpaceSize).toOption.toJson,
          "swap_space_free" -> Try(unixOs.getFreeSwapSpaceSize).toOption.toJson,
          "max_fd_count" -> Try(unixOs.getMaxFileDescriptorCount).toOption.toJson,
          "open_fd_count" -> Try(unixOs.getOpenFileDescriptorCount).toOption.toJson
        )

      // No extra information to collect on non-Unix systems.
      case _ =>
    }

    result.toMap
  }

  private def getVmInfo(normalTermination: Boolean) = {
    val runtime = management.ManagementFactory.getRuntimeMXBean

    Map(
      "name" -> runtime.getVmName.toJson,
      "vendor" -> runtime.getVmVendor.toJson,
      "version" -> runtime.getVmVersion.toJson,
      "spec_name" -> runtime.getSpecName.toJson,
      "spec_vendor" -> runtime.getSpecVendor.toJson,
      "spec_version" -> runtime.getSpecVersion.toJson,
      "mode" -> systemPropertyAsJson("java.vm.info"),
      "compressed_oops_mode" -> systemPropertyAsJson("java.vm.compressedOopsMode"),
      "args" -> runtime.getInputArguments.asScala.toList.toJson,
      "termination" -> (if (normalTermination) "normal" else "forced").toJson,
      "start_unix_ms" -> runtime.getStartTime.toJson,
      "start_iso" -> unixTimeAsIso(runtime.getStartTime).toJson,
      "uptime_ms" -> runtime.getUptime.toJson,
      "collectors" -> getCollectorInfo.toJson,
      "compiler" -> getCompilationInfo.toJson,
      "classloading" -> getClassLoadingInfo.toJson,
      "memory" -> getMemoryInfo.toJson,
      "pools" -> getMemoryPoolInfo.toJson,
      "threads" -> getThreadInfo.toJson
    )
  }

  private def getJreInfo = {
    val runtime = management.ManagementFactory.getRuntimeMXBean

    val result = mutable.Buffer(
      "name" -> systemPropertyAsJson("java.runtime.name"),
      "version" -> systemPropertyAsJson("java.runtime.version"),
      "java_vendor" -> systemPropertyAsJson("java.vendor"),
      "java_version" -> systemPropertyAsJson("java.version"),
      "spec_name" -> systemPropertyAsJson("java.specification.name"),
      "spec_vendor" -> systemPropertyAsJson("java.specification.vendor"),
      "spec_version" -> systemPropertyAsJson("java.specification.version"),
      "home" -> systemPropertyAsJson("java.home"),
      "library_path" -> pathsAsJson(runtime.getLibraryPath),
      "class_path" -> pathsAsJson(runtime.getClassPath)
    )

    if (runtime.isBootClassPathSupported) {
      result += ("boot_class_path" -> pathsAsJson(runtime.getBootClassPath))
    }

    result.toMap
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
    val memory = management.ManagementFactory.getMemoryMXBean

    Map(
      "heap_usage" -> getMemoryUsageInfo(memory.getHeapMemoryUsage).toJson,
      "nonheap_usage" -> getMemoryUsageInfo(memory.getNonHeapMemoryUsage).toJson,
      "pending_finalization_count" -> memory.getObjectPendingFinalizationCount.toJson
    )
  }

  private def getMemoryPoolInfo = {
    management.ManagementFactory.getMemoryPoolMXBeans.asScala
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
    management.ManagementFactory.getGarbageCollectorMXBeans.asScala
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
    // Compilation MX Bean is not available in interpreted mode.
    Option(management.ManagementFactory.getCompilationMXBean).map(info => {
      val result = mutable.Buffer(
        "name" -> info.getName.toJson
      )

      if (info.isCompilationTimeMonitoringSupported) {
        result += ("compilation_time_ms" -> info.getTotalCompilationTime.toJson)
      }

      result.toMap
    })
  }

  private def getClassLoadingInfo = {
    val classLoading = management.ManagementFactory.getClassLoadingMXBean

    Map(
      "class_count" -> classLoading.getLoadedClassCount.toJson,
      "classes_total" -> classLoading.getTotalLoadedClassCount.toJson
    )
  }

  private def getThreadInfo = {
    val threads = management.ManagementFactory.getThreadMXBean

    Map(
      "thread_count" -> threads.getThreadCount.toJson,
      "thread_count_max" -> threads.getPeakThreadCount.toJson,
      "daemon_thread_count" -> threads.getDaemonThreadCount.toJson,
      "threads_total" -> threads.getTotalStartedThreadCount.toJson
    )
  }

  private def getSuiteInfo = {
    val manifest = {
      val benchClass = classOf[Benchmark]
      val stream = benchClass.getResourceAsStream("/META-INF/MANIFEST.MF")
      new java.util.jar.Manifest(stream)
    }

    def manifestAttrAsJson(key: String, defaultValue: String = null) = {
      Option(manifest.getMainAttributes.getValue(key)).orElse(Option(defaultValue)).toJson
    }

    val gitInfo = Map(
      "commit_hash" -> manifestAttrAsJson("Git-Head-Commit"),
      "commit_date" -> manifestAttrAsJson("Git-Head-Commit-Date"),
      "dirty" -> manifestAttrAsJson("Git-Uncommitted-Changes", "true")
    )

    //

    Map(
      "git" -> gitInfo.toJson,
      "name" -> manifestAttrAsJson("Specification-Title"),
      "version" -> manifestAttrAsJson("Specification-Version")
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

    writeToFile(jsonFile, result.toJson.prettyPrint)
  }

  private def getResultData = {
    val metricNames = getMetricNames

    val dataTree = mutable.Map[String, JsValue]()
    for ((benchmark, benchFailed, metricsByName, repetitionCount) <- getBenchmarkResults) {
      // For each repetition, collect (name -> value) tuples for metrics into a map.
      val repetitions = (0 until repetitionCount).map(i =>
        metricNames
          .flatMap(name => metricsByName.get(name).map(values => name -> values(i).toJson))
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
