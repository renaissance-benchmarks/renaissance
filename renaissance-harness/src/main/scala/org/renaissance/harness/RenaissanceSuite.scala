package org.renaissance.harness

import java.util.concurrent.TimeUnit.SECONDS
import java.util.function.ToIntFunction

import org.renaissance.Benchmark
import org.renaissance.BenchmarkResult.ValidationException
import org.renaissance.Plugin
import org.renaissance.Plugin.ExecutionPolicy
import org.renaissance.core.BenchmarkInfo
import org.renaissance.core.BenchmarkRegistry
import org.renaissance.core.ModuleLoader
import org.renaissance.core.ModuleLoader.ModuleLoadingException
import org.renaissance.harness.ExecutionPolicies.FixedOpCount
import org.renaissance.harness.ExecutionPolicies.FixedOpTime
import org.renaissance.harness.ExecutionPolicies.FixedTime

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

    // Load information about available benchmarks.
    val allBenchmarks = BenchmarkRegistry.createDefault()

    if (config.printList) {
      print(formatBenchmarkList(allBenchmarks))
    } else if (config.printRawList) {
      println(formatRawBenchmarkList(allBenchmarks))
    } else if (config.printGroupList) {
      println(formatGroupList(allBenchmarks))
    } else if (config.benchmarkSpecifiers.isEmpty) {
      println(parser.usage())
    } else {
      val benchmarks = selectBenchmarks(allBenchmarks, config.benchmarkSpecifiers)

      // Load all plugins in given order (including external policy).
      val externalPlugins = for ((specifier, args) <- config.pluginsWithArgs) yield {
        specifier -> createExtension(specifier, args)
      }

      //
      // Get effective execution policy (built-in or external) and if using
      // a built-in policy, prepend it to list of plugins (external policy
      // will be among the external plugins specified on the command line).
      //
      var plugins = externalPlugins.values.toSeq

      val policy = getPolicy(config, benchmarks, externalPlugins)
      if (config.policyType != PolicyType.EXTERNAL) {
        plugins = policy +: plugins
      }

      //
      // (Optionally) register the built-in plugin to force GC before each
      // measured operation. The plugin has the lowest priority and is the
      // first to be executed 'before operation', preceding the built-in
      // policies.
      //
      if (config.forceGc) {
        plugins = new ExecutionPlugins.ForceGcPlugin() +: plugins
      }

      // Initialize result writers (if any).
      val writers = Seq(
        config.csvOutput.map(f => new CsvWriter(f)),
        config.jsonOutput.map(f => new JsonWriter(f))
      ).flatten

      // Register plugins and result writers for harness events.
      val dispatcher = createEventDispatcher(plugins, writers)

      // Note: no access to Config beyond this point.
      runBenchmarks(benchmarks, config.configuration, policy, dispatcher)
    }
  }

  private def runBenchmarks(
    benchmarks: Seq[BenchmarkInfo],
    configurationName: String,
    policy: ExecutionPolicy,
    dispatcher: EventDispatcher
  ): Unit = {
    // TODO: Why collect failing benchmarks instead of just quitting whenever one fails?
    val failedBenchmarks = new mutable.ArrayBuffer[BenchmarkInfo](benchmarks.length)

    // Notify observers that the suite is set up.
    dispatcher.notifyAfterHarnessInit()

    try {
      for (benchInfo <- benchmarks) {
        val benchmark = BenchmarkRegistry.loadBenchmark(benchInfo)
        val driver = new ExecutionDriver(benchInfo, configurationName)

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

  private def createEventDispatcher(plugins: Iterable[Plugin], writers: Seq[ResultWriter]) = {
    val builder = new EventDispatcher.Builder

    // Register plugins first
    plugins.foreach(builder.withPlugin)

    // Result writers go after plugins
    writers.foreach(builder.withResultWriter)

    builder.build()
  }

  private def createExtension[T](
    specifier: String,
    args: mutable.Seq[String]
  ) = {
    try {
      val specifierParts = specifier.trim.split("!", 2)
      val (classPath, className) = (specifierParts(0), specifierParts(1))
      val extClass = ModuleLoader.loadExtension(classPath, className, classOf[Plugin])
      ModuleLoader.createExtension(extClass, args.toArray[String])
    } catch {
      case e: ModuleLoadingException =>
        Console.err.println(s"Error: failed to load plugin '$specifier': ${e.getMessage}")
        sys.exit(1)
    }
  }

  private def getPolicy(
    config: Config,
    benchmarks: Seq[BenchmarkInfo],
    plugins: Map[String, Plugin]
  ): ExecutionPolicy = {
    config.policyType match {
      case PolicyType.FIXED_OP_COUNT =>
        val countProvider: ToIntFunction[String] = if (config.repetitions.isDefined) {
          // Global repetition count is set, overrides benchmark defaults
          _: String =>
            config.repetitions.get
        } else {
          // Global repetition count is unset, get default value from benchmark
          name: String =>
            benchmarks.find(info => info.name == name).get.repetitions()
        }

        new FixedOpCount(countProvider)

      case PolicyType.FIXED_OP_TIME =>
        new FixedOpTime(SECONDS.toNanos(config.runSeconds))

      case PolicyType.FIXED_TIME =>
        new FixedTime(SECONDS.toNanos(config.runSeconds))

      case PolicyType.EXTERNAL =>
        plugins(config.policyPlugin) match {
          case policy: ExecutionPolicy => policy
          case _ =>
            Console.err.println(
              s"Error: '${config.policyPlugin}' does not implement ${classOf[ExecutionPolicy].getName}"
            )
            sys.exit(1)
        }
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
      val summaryWords = bench.summary().split("\\s+")
      result.append(foldText(summaryWords, 65, indent).mkString("\n")).append("\n")
      result.append(s"${indent}Default repetitions: ${bench.repetitions}").append("\n\n")
    }

    result.toString
  }

  private def formatGroupList(benchmarks: BenchmarkRegistry) =
    benchmarks.groupNames().asScala.sorted.mkString("\n")

}
