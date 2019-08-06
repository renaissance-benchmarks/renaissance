package org.renaissance.harness

import org.renaissance.Benchmark
import org.renaissance.BenchmarkResult.ValidationException
import org.renaissance.core.BenchmarkInfo
import org.renaissance.core.BenchmarkRegistry
import org.renaissance.core.ModuleLoader
import org.renaissance.core.ModuleLoader.ModuleLoadingException

import scala.collection.JavaConverters._
import scala.collection._

object RenaissanceSuite {

  def main(args: Array[String]): Unit = {
    val benchmarkPkg = classOf[Benchmark].getPackage
    val parser = new ConfigParser(
      immutable.Map(
        "renaissanceTitle" -> benchmarkPkg.getSpecificationTitle,
        "renaissanceVersion" -> benchmarkPkg.getImplementationVersion
      )
    )

    val config = parser.parse(args) match {
      case Some(c) => c
      case None    => sys.exit(1)
    }

    // Load info on available benchmarks
    val benchmarks = BenchmarkRegistry.createDefault()

    if (config.printList) {
      print(formatBenchmarkList(benchmarks))
    } else if (config.printRawList) {
      println(formatRawBenchmarkList(benchmarks))
    } else if (config.printGroupList) {
      println(formatGroupList(benchmarks))
    } else if (config.benchmarkSpecifiers.isEmpty) {
      println(parser.usage())
    } else {
      // Select the desired benchmarks and check that they really exist.
      val specifiers = config.benchmarkSpecifiers.asScala
      val selectedBenchmarks = selectBenchmarks(benchmarks, specifiers)

      // Load plugins, init writers, and sign them up for events
      val dispatcher = createEventDispatcher(config)

      runBenchmarks(selectedBenchmarks, dispatcher, config)
    }
  }

  private def runBenchmarks(
    benchmarks: Seq[BenchmarkInfo],
    dispatcher: EventDispatcher,
    config: Config
  ): Unit = {
    // TODO: Why collect failing benchmarks instead of just quitting whenever one fails?
    val failedBenchmarks = new mutable.ArrayBuffer[BenchmarkInfo](benchmarks.length)

    // Notify observers that the suite is set up.
    dispatcher.notifyAfterHarnessInit()

    try {
      for (benchInfo <- benchmarks) {
        val benchmark = BenchmarkRegistry.loadBenchmark(benchInfo)
        val driver = new ExecutionDriver(benchInfo, config.configuration)

        // Create execution policy
        val policy = config.policyFactory.create(config, benchInfo)

        try {
          driver.executeBenchmark(benchmark, dispatcher, policy)

        } catch {
          case t: Throwable =>
            // Notify observers that a benchmark failed.
            dispatcher.notifyOnBenchmarkFailure(benchInfo.name)
            failedBenchmarks += benchInfo

            t match {
              case _: ValidationException =>
                Console.err.println(
                  s"Benchmark '${benchInfo.name()}' failed result validation:\n${t.getMessage}"
                )

              case _ =>
                Console.err.println(s"Benchmark '${benchInfo.name()}' failed with exception:")
                t.printStackTrace(Console.err)
            }
        }
      }

    } finally {
      // Notify listeners that the suite is shutting down.
      dispatcher.notifyBeforeHarnessShutdown()

      if (failedBenchmarks.nonEmpty) {
        val failedBenchmarksList = failedBenchmarks.map(_.name()).mkString(", ")
        println(s"The following benchmarks failed: $failedBenchmarksList")
        sys.exit(1)
      }
    }
  }

  def selectBenchmarks(
    benchmarks: BenchmarkRegistry,
    specifiers: Seq[String]
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
        result ++= benchmarks.getAll.asScala.filter(_.group != "dummy")
      } else {
        Console.err.println(s"Benchmark (or group) '$specifier' does not exist.")
        sys.exit(1)
      }
    }

    result.toSeq
  }

  private def createEventDispatcher(config: Config) = {
    val dispatcherBuilder = new EventDispatcher.Builder

    for ((specifier, args) <- config.pluginsWithArgs.asScala) {
      dispatcherBuilder.withPlugin(loadPlugin(specifier, args))
    }

    // Result writers go after plugins
    if (config.csvOutput != null) {
      dispatcherBuilder.withResultWriter(new CsvWriter(config.csvOutput))
    }

    if (config.jsonOutput != null) {
      dispatcherBuilder.withResultWriter(new JsonWriter(config.jsonOutput))
    }

    dispatcherBuilder.build()
  }

  private def loadPlugin(specifier: String, args: java.util.List[String]) = {
    try {
      val specifierParts = specifier.trim.split("!", 2)
      val (classPath, className) = (specifierParts(0), specifierParts(1))
      ModuleLoader.loadPlugin(classPath, className, args.toArray(Array[String]()))
    } catch {
      case e: ModuleLoadingException =>
        Console.err.println(s"Error: failed to load plugin '$specifier': ${e.getMessage}")
        sys.exit(1)
    }
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
  }

  private def formatRawBenchmarkList(benchmarks: BenchmarkRegistry) =
    benchmarks.names().asScala.mkString("\n")

  private def formatBenchmarkList(benchmarks: BenchmarkRegistry) = {
    val indent = "    "

    val result = new StringBuilder
    for (bench <- benchmarks.getAll.asScala) {
      result.append(bench.name).append("\n")
      result.append(foldText(bench.summaryWords, 65, indent).mkString("\n")).append("\n")
      result.append(s"${indent}Default repetitions: ${bench.repetitions}").append("\n\n")
    }

    result.toString
  }

  private def formatGroupList(benchmarks: BenchmarkRegistry) =
    benchmarks.groupNames().asScala.sorted.mkString("\n")

}
