package org.renaissance.harness

import org.renaissance.BenchmarkResult.ValidationException
import org.renaissance.Plugin.ExecutionPolicy
import org.renaissance.core.ModuleLoader.ModuleLoadingException
import org.renaissance.core.{BenchmarkInfo, BenchmarkRegistry, DirUtils, ModuleLoader, Version}
import org.renaissance.harness.ExecutionPolicies.{FixedOpCount, FixedOpTime, FixedTime}
import org.renaissance.{Benchmark, Plugin}

import java.lang.management.ManagementFactory
import java.nio.file.Path
import java.util.concurrent.TimeUnit.{MILLISECONDS, SECONDS}
import java.util.function.ToIntFunction
import java.util.{Locale, Optional}
import scala.collection._
import scala.jdk.CollectionConverters._

object RenaissanceSuite {

  def main(args: Array[String]): Unit = {
    // Ensure repeatable output across different environments.
    Locale.setDefault(Locale.ROOT)

    val benchmarkPkg = classOf[Benchmark].getPackage
    val parser = new ConfigParser(
      immutable.Map(
        "renaissanceTitle" -> benchmarkPkg.getSpecificationTitle,
        "renaissanceVersion" -> benchmarkPkg.getImplementationVersion
      )
    )

    val config = parser.parse(args) match {
      case Some(c) => c
      case None => sys.exit(1)
    }

    // Create harness scratch directory in scratch base.
    val scratchRoot = DirUtils.createScratchDirectory(
      config.scratchBase,
      "harness-",
      config.keepScratch
    )

    // Load information about available benchmarks.
    val benchmarkRegistry = BenchmarkRegistry.createDefault()
    val realBenchmarks = benchmarkRegistry.getMatching(benchmarkIsReal).asScala

    if (config.printList) {
      print(formatBenchmarkList(realBenchmarks))
    } else if (config.printRawList) {
      val jvmVersion = Version.parse(ManagementFactory.getRuntimeMXBean.getSpecVersion)
      val listedBenchmarks =
        if (config.checkJvm) realBenchmarks.filter(benchmarkIsCompatible(_, jvmVersion))
        else realBenchmarks
      print(formatRawBenchmarkList(listedBenchmarks))
    } else if (config.printGroupList) {
      print(formatGroupList(realBenchmarks))
    } else if (config.benchmarkSpecifiers.isEmpty) {
      print(parser.usage())
    } else {
      // Collect specified benchmarks compatible with the JVM.
      var benchmarks = selectBenchmarks(benchmarkRegistry, config.benchmarkSpecifiers)
      if (config.checkJvm) {
        benchmarks = excludeIncompatible(benchmarks)
      }

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
      runBenchmarks(benchmarks, config.configuration, scratchRoot, policy, dispatcher)
    }
  }

  private def runBenchmarks(
    benchmarks: Seq[BenchmarkInfo],
    configurationName: String,
    scratchRoot: Path,
    policy: ExecutionPolicy,
    dispatcher: EventDispatcher
  ): Unit = {
    // Initialize harness module loader.
    val moduleLoader = ModuleLoader.create(scratchRoot)

    // TODO: Why collect failing benchmarks instead of just quitting whenever one fails?
    val failedBenchmarks = new mutable.ArrayBuffer[BenchmarkInfo](benchmarks.length)

    val vmStartNanos = getVmStartNanos

    // Notify observers that the suite is set up.
    dispatcher.notifyAfterHarnessInit()

    try {
      for (benchInfo <- benchmarks) {
        val benchmark = benchInfo.loadBenchmarkModule(moduleLoader)
        val driver =
          new ExecutionDriver(benchInfo, configurationName, scratchRoot, vmStartNanos)

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

  private def getVmStartNanos = {
    //
    // Get two nanoTime() samples around currentTimeMillis() that are as
    // close as possible to when the currentTimeMillis() result flips. Use
    // the two straddling nanoTime() readings as an estimate of nanoTime()
    // corresponding to the last currentTimeMillis() result.
    //
    // Repeat to minimize the difference between the two nanoTime() readings
    // and stop when no improvement has been observed for several iterations.
    //
    // This avoids basing the estimate on first calls to native methods which
    // tend to be slow, and has a chance to avoid scheduling artifacts.
    //
    val streakLengthMax = 10

    var syncNanos = 0L
    var syncMillis = 0L

    var nanosDiffMin = Long.MaxValue
    var streakLength = 0
    do {
      var nanosBefore = 0L
      var currentMillis = 0L

      val lastMillis = System.currentTimeMillis()
      var nanosAfter = System.nanoTime()

      do {
        nanosBefore = nanosAfter
        currentMillis = System.currentTimeMillis()
        nanosAfter = System.nanoTime()
      } while (currentMillis == lastMillis)

      streakLength += 1

      val nanosDiff = nanosAfter - nanosBefore
      if (nanosDiff < nanosDiffMin) {
        nanosDiffMin = nanosDiff
        streakLength = 0

        // Record the corresponding nanoTime() estimate.
        syncNanos = (nanosBefore + nanosAfter) / 2
        syncMillis = currentMillis
      }
    } while (streakLength < streakLengthMax)

    //
    // Approximate nanoTime() value at VM start based on the millisecond
    // timestamp available from the Runtime MX Bean.
    //
    val vmStartMillis = management.ManagementFactory.getRuntimeMXBean.getStartTime
    val uptimeMillis = syncMillis - vmStartMillis
    syncNanos - MILLISECONDS.toNanos(uptimeMillis)
  }

  private def selectBenchmarks(
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
        result ++= benchmarks.getMatching(benchmarkIsReal).asScala
      } else {
        Console.err.println(s"Benchmark (or group) '$specifier' does not exist.")
        sys.exit(1)
      }
    }

    result.toSeq
  }

  private def excludeIncompatible(benchmarks: Seq[BenchmarkInfo]): Seq[BenchmarkInfo] = {
    def versionRange(b: BenchmarkInfo) = {
      val result = new StringBuilder

      b.jvmVersionMin().ifPresent(v => result.append(s">=$v"))

      b.jvmVersionMax()
        .ifPresent(v => {
          if (result.nonEmpty) {
            result.append(" and ")
          }

          result.append(s"<=$v")
        })

      result
    }

    val jvmVersion = Version.parse(ManagementFactory.getRuntimeMXBean.getSpecVersion)

    // Exclude incompatible benchmarks with a warning.
    benchmarks
      .filter(b => {
        val isCompatible = benchmarkIsCompatible(b, jvmVersion)
        if (!isCompatible) {
          Console.err.println(
            s"Benchmark '${b.name()}' excluded: requires JVM version ${versionRange(b)} (found $jvmVersion)."
          )
        }

        isCompatible
      })
      .toSeq
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

  private def formatRawBenchmarkList(benchmarks: Seq[BenchmarkInfo]) =
    benchmarks.map(_.name() + "\n").mkString

  private def formatBenchmarkList(benchmarks: Seq[BenchmarkInfo]) = {
    val indent = "    "
    val jvmVersion = Version.parse(ManagementFactory.getRuntimeMXBean.getSpecVersion)

    val result = new StringBuilder
    for (bench <- benchmarks) {
      result.append(bench.name)
      if (!benchmarkIsCompatible(bench, jvmVersion)) {
        result.append(s" (not compatible with this JVM)")
      }
      result.append("\n")

      val summaryWords = bench.summary().split("\\s+")
      result.append(foldText(summaryWords, 65, indent).mkString("\n")).append("\n")

      bench
        .jvmVersionMin()
        .ifPresent(v => {
          result.append(s"${indent}Minimum JVM version required: $v")
          if (jvmVersion.compareTo(v) < 0) {
            result.append(s" (found $jvmVersion)");
          }
          result.append("\n")
        })

      bench
        .jvmVersionMax()
        .ifPresent(v => {
          result.append(s"${indent}Maximum JVM version supported: $v")
          if (jvmVersion.compareTo(v) > 0) {
            result.append(s" (found $jvmVersion)");
          }
          result.append("\n")
        })

      result.append(s"${indent}Default repetitions: ${bench.repetitions}").append("\n")
      result.append("\n")
    }

    result.toString
  }

  private def formatGroupList(benchmarks: Seq[BenchmarkInfo]) =
    benchmarks.flatMap(_.groups()).distinct.sorted.map(_ + "\n").mkString

  private def benchmarkIsReal(b: BenchmarkInfo) = {
    !b.groups().contains("dummy")
  }

  private def benchmarkIsCompatible(b: BenchmarkInfo, jvmVersion: Version) = {
    def compare(v1: Version, maybeV2: Optional[Version]) =
      maybeV2.map((v2: Version) => v1.compareTo(v2)).orElse(0)

    val minSatisfied = compare(jvmVersion, b.jvmVersionMin) >= 0
    val maxSatisfied = compare(jvmVersion, b.jvmVersionMax) <= 0
    minSatisfied && maxSatisfied
  }

}
