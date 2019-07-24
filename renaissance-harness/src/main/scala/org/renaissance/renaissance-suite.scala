package org.renaissance

import org.renaissance.util.BenchmarkInfo
import org.renaissance.util.BenchmarkRegistry

import scala.collection._
import scala.collection.JavaConverters._

object RenaissanceSuite {


  def main(args: Array[String]): Unit = {
    val benchmarkPkg = classOf[Benchmark].getPackage
    val parser = new ConfigParser(
      immutable.Map(
        "renaissanceTitle" -> benchmarkPkg.getImplementationTitle,
        "renaissanceVersion" -> benchmarkPkg.getImplementationVersion
      )
    )

    val config = parser.parse(args) match {
      case Some(c) => c
      case None    => sys.exit(1)
    }

    // Load info on available benchmarks
    val benchmarks = BenchmarkRegistry.createDefault();

    if (config.printList) {
      print(formatBenchmarkList(benchmarks))
    } else if (config.printRawList) {
      println(formatRawBenchmarkList(benchmarks))
    } else if (config.printGroupList) {
      println(formatGroupList(benchmarks))
    } else if (config.benchmarkSpecifiers.isEmpty) {
      println(parser.usage)
    } else {
      // Select the desired benchmarks and check that they really exist.
      val specifiers = config.benchmarkSpecifiers.asScala
      val selectedBenchmarks = selectBenchmarks(specifiers, benchmarks)
      runBenchmarks(selectedBenchmarks, config)
    }
  }

  private def runBenchmarks(benchmarks: Seq[BenchmarkInfo], config: Config): Unit = {
    val failedBenchmarks = new mutable.ArrayBuffer[BenchmarkInfo](benchmarks.length)

      // Run the main benchmark loop.
      for (plugin <- config.plugins.asScala) plugin.onCreation()

    try {
      for (benchInfo <- benchmarks) {
        val bench = benchInfo.loadBenchmark()

          val exception = bench.runBenchmark(config)
          if (exception != null) {
            failedBenchmarks += benchInfo
            Console.err.println(s"Exception occurred in ${bench}: ${exception.getMessage}")
            exception.printStackTrace()
          }
        }
        for (plugin <- config.plugins.asScala) plugin.onExit()
        for (observer <- config.resultObservers.asScala) observer.onExit()
      }

    } finally {

      if (failedBenchmarks.nonEmpty) {
        println(s"The following benchmarks failed: ${failedBenchmarks.mkString(", ")}")
        sys.exit(1)
      }
    }
  }

  def selectBenchmarks(
    specifiers: Seq[String],
    benchmarks: BenchmarkRegistry
  ): Seq[BenchmarkInfo] = {
    val result = new mutable.LinkedHashSet[BenchmarkInfo]
    for (specifier <- specifiers) {
      if (benchmarks.exists(specifier)) {
        // Add an individual benchmark
        result += benchmarks.get(specifier)
      } else if (benchmarks.groupExists(specifier)) {
        // Add benchmarks for a given group
        result ++= benchmarks.getGroup(specifier).asScala
      } else if (specifier == "all") {
        // Add all benchmarks except the dummy ones
        result ++= benchmarks.getAll().asScala.filter(_.group != "dummy")
      } else {
        println(s"Benchmark (or group) `${specifier}` does not exist.")
        sys.exit(1)
      }
    }

    result.toSeq
  }

  def foldText(words: Seq[String], width: Int, indent: String): Seq[String] = {
    var column = 0
    val line = new StringBuffer
    val result = new mutable.ArrayBuffer[String]
    for (word <- words) {
      if ((column + word.length + 1 >= width) && (column > 0)) {
        result += line.toString
        line.setLength(0)
        column = 0
      }
      if (column > 0) {
        line.append(" ")
      } else {
        line.append(indent)
      }
      line.append(word)
      column += word.length
    }
    result += line.toString
    return result
  }

  private def formatRawBenchmarkList(benchmarks: BenchmarkRegistry) =
    benchmarks.names().asScala.mkString("\n")

  private def formatBenchmarkList(benchmarks: BenchmarkRegistry) = {
    val indent = "    "

    val result = new StringBuffer
    for (bench <- benchmarks.getAll().asScala) {
      result.append(bench.name).append("\n")
      result.append(foldText(bench.summaryWords, 65, indent).mkString("\n")).append("\n")
      result.append(s"${indent}Default repetitions: ${bench.repetitions}").append("\n\n")
    }

    result.toString
  }

  private def formatGroupList(benchmarks: BenchmarkRegistry) =
    benchmarks.groupNames().asScala.sorted.mkString("\n")

}
