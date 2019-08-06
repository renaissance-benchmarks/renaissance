package org.renaissance.harness

import java.util
import java.util.concurrent.TimeUnit.SECONDS

import org.renaissance.Benchmark
import org.renaissance.BenchmarkResult.ValidationException
import org.renaissance.ExecutionPolicy
import org.renaissance.Plugin
import org.renaissance.core.BenchmarkInfo
import org.renaissance.core.BenchmarkRegistry
import org.renaissance.core.ModuleLoader
import org.renaissance.core.ModuleLoader.ModuleLoadingException

import scala.annotation.switch
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

      // Load external policy (if any) and create policy factory
      val policyFactory = createPolicyFactory(config)

      // Load plugins, init writers, and sign them up for events
      val dispatcher = createEventDispatcher(config)

      runBenchmarks(selectedBenchmarks, config.configuration, policyFactory, dispatcher)
    }
  }

  private def runBenchmarks(
    benchmarks: Seq[BenchmarkInfo],
    configurationName: String,
    policyFactory: BenchmarkInfo => ExecutionPolicy,
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

        // Create execution policy
        val policy = policyFactory(benchInfo)

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
      dispatcherBuilder.withPlugin(createPlugin(specifier, args))
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

  private def createPlugin(specifier: String, args: java.util.List[String]) = {
    try {
      createExtensionFactory(specifier, args, classOf[Plugin]).getInstance()
    } catch {
      case e @ (_: ModuleLoadingException | _: ReflectiveOperationException) =>
        Console.err.println(s"Error: failed to load plugin '$specifier': ${e.getMessage}")
        sys.exit(1)
    }
  }

  private def createPolicyFactory(config: Config): BenchmarkInfo => ExecutionPolicy = {
    config.policyType match {
      case Config.PolicyType.FIXED_OP_COUNT =>
        val repetitions = config.repetitions
        (benchInfo: BenchmarkInfo) => {
          val count = if (repetitions > 0) repetitions else benchInfo.repetitions()
          ExecutionPolicies.fixedCount(count);
        }

      case Config.PolicyType.FIXED_OP_TIME =>
        val runNanos = SECONDS.toNanos(config.runSeconds)
        (benchInfo: BenchmarkInfo) => ExecutionPolicies.fixedOperationTime(runNanos)

      case Config.PolicyType.FIXED_TIME =>
        val runNanos = SECONDS.toNanos(config.runSeconds)
        (benchInfo: BenchmarkInfo) => ExecutionPolicies.fixedTime(runNanos);

      case Config.PolicyType.EXTERNAL =>
        try {
          val policyFactory = createExtensionFactory(
            config.externalPolicy,
            config.externalPolicyArgs,
            classOf[ExecutionPolicy]
          )
          (benchInfo: BenchmarkInfo) => policyFactory.getInstance()

        } catch {
          case e @ (_: ModuleLoadingException | _: ReflectiveOperationException) =>
            Console.err.println(
              s"Error: failed to load policy '${config.externalPolicy}': ${e.getMessage}"
            )
            sys.exit(1)
        }
    }
  }

  private def createExtensionFactory[T](
    specifier: String,
    args: util.List[String],
    baseClass: Class[T]
  ) = {
    val specifierParts = specifier.trim.split("!", 2)
    val (classPath, className) = (specifierParts(0), specifierParts(1))
    val extClass = ModuleLoader.loadExtension(classPath, className, baseClass)
    ModuleLoader.createFactory(extClass, args.toArray(Array[String]()))
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
