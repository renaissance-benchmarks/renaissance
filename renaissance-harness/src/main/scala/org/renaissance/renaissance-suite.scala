package org.renaissance

import org.renaissance.util.BenchmarkLoader
import org.renaissance.util.BenchmarkRegistry
import scopt._

import scala.collection._
import scala.collection.JavaConverters._

object RenaissanceSuite {

  val parser: OptionParser[Config] =
    new OptionParser[Config]("renaissance") {
      val pkg = classOf[Benchmark].getPackage
      val title = pkg.getSpecificationTitle
      val version = pkg.getImplementationVersion

      head(s"${title}, version ${version}")

      help('h', "help")
        .text("Prints this usage text.")
      opt[Int]('r', "repetitions")
        .text("Number of repetitions used with the fixed-iterations policy.")
        .action((v, c) => c.withRepetitions(v))
      opt[Int]('w', "warmup-seconds")
        .text("Number of warmup seconds, when using time-based policies.")
        .action((v, c) => c.withWarmupSeconds(v))
      opt[Int]('t', "run-seconds")
        .text("Number of seconds to run after the warmup, when using time-based policies.")
        .action((v, c) => c.withRunSeconds(v))
      opt[String]("policy")
        .text(
          "Execution policy, one of: " + Policy.descriptions.asScala.keys.mkString(", ")
        )
        .action((v, c) => c.withPolicy(v))
      opt[String]("plugins")
        .text("Comma-separated list of class names of plugin implementations.")
        .action((v, c) => c.withPlugins(v))
      opt[String]("csv")
        .text("Output results to CSV file.")
        .action((v, c) => c.withResultObserver(new CsvWriter(v)))
      opt[String]("json")
        .text("Output results to JSON file.")
        .action((v, c) => c.withResultObserver(new JsonWriter(v)))
      opt[Unit]("functional-test")
        .text("Reduce iteration times significantly for testing purposes.")
        .action((_, c) => c.withFunctionalTest())
      opt[Unit]("list")
        .text("Print list of benchmarks with their description.")
        .action((_, c) => c.withList())
      opt[Unit]("raw-list")
        .text("Print list of benchmarks (each benchmark name on separate line).")
        .action((_, c) => c.withRawList())
      opt[Unit]("group-list")
        .text("Print list of benchmark groups (each group name on separate line).")
        .action((_, c) => c.withGroupList())
      arg[String]("benchmark-specification")
        .text("Comma-separated list of benchmarks (or groups) that must be executed (or all).")
        .optional()
        .action((v, c) => c.withBenchmarkSpecification(v))
    }

  private def parse(args: Array[String]): Option[Config] = {
    parser.parse(args, new Config)
  }

  def main(args: Array[String]): Unit = {
    val config = parse(args) match {
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
      // Check that all the benchmarks on the list really exist.
      val selectedBenchmarks = getSelectedBenchmarks(config, benchmarks)

      // Run the main benchmark loop.
      for (plugin <- config.plugins.asScala) plugin.onCreation()

      val failedBenchmarks = new mutable.ArrayBuffer[String](selectedBenchmarks.length)

      try {
        val benchmarkLoader = new BenchmarkLoader(benchmarks)

        for (benchName <- selectedBenchmarks) {
          val bench = benchmarkLoader.loadBenchmark(benchName)
          val exception = bench.runBenchmark(config)
          if (exception != null) {
            failedBenchmarks += benchName
            Console.err.println(s"Exception occurred in ${bench}: ${exception.getMessage}")
            exception.printStackTrace()
          }
        }

      } finally {
        for (plugin <- config.plugins.asScala) plugin.onExit()
        for (observer <- config.resultObservers.asScala) observer.onExit()
      }

      if (failedBenchmarks.nonEmpty) {
        println(s"The following benchmarks failed: ${failedBenchmarks.mkString(", ")}")
        sys.exit(1)
      }
    }
  }

  def getSelectedBenchmarks(config: Config, benchmarks: BenchmarkRegistry): Seq[String] = {
    val result = new mutable.LinkedHashSet[String]
    for (specifier <- config.benchmarkSpecifiers.asScala) {
      if (benchmarks.exists(specifier)) {
        // Add an individual benchmark
        result += specifier
      } else if (benchmarks.groupExists(specifier)) {
        // Add benchmarks for a given group
        result ++= benchmarks.getGroup(specifier).asScala.map(_.name)
      } else if (specifier == "all") {
        // Add all benchmarks except the dummy ones
        result ++= benchmarks.getAll().asScala.filter(_.group != "dummy").map(_.name)
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
