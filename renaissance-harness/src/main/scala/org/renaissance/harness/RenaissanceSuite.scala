package org.renaissance.harness

import org.renaissance.Benchmark
import org.renaissance.BenchmarkResult.ValidationException
import org.renaissance.Plugin
import org.renaissance.Plugin.ExecutionPolicy
import org.renaissance.core.BenchmarkDescriptor
import org.renaissance.core.BenchmarkSuite
import org.renaissance.core.BenchmarkSuite.ExtensionException
import org.renaissance.core.BenchmarkSuite.getManifestUseModulesValue
import org.renaissance.core.BenchmarkSuite.jvmSpecVersion
import org.renaissance.core.DirUtils
import org.renaissance.harness.ExecutionPolicies.FixedOpCount
import org.renaissance.harness.ExecutionPolicies.FixedOpTime
import org.renaissance.harness.ExecutionPolicies.FixedTime

import java.io.File
import java.io.IOException
import java.io.PrintStream
import java.nio.file.Files
import java.nio.file.Path
import java.nio.file.Paths
import java.util.Locale
import java.util.concurrent.TimeUnit.MILLISECONDS
import java.util.concurrent.TimeUnit.SECONDS
import java.util.function.ToIntFunction
import scala.collection._
import scala.jdk.CollectionConverters._
import scala.util.Failure
import scala.util.Success
import scala.util.Try

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
      case Some(parsedConfig) => parsedConfig
      case None => sys.exit(1)
    }

    // Create harness scratch directory in scratch base.
    val scratchRoot = DirUtils.createScratchDirectory(
      config.scratchBase,
      "harness-",
      config.keepScratch
    )

    // Create benchmark suite core.
    val suite: BenchmarkSuite = Try(
      BenchmarkSuite.create(
        scratchRoot,
        config.configuration,
        config.benchmarkMetadataOverrideUri,
        config.parameterOverrides.asJava,
        getManifestUseModulesValue.orElse(config.useModules)
      )
    ) match {
      case Success(suite) => suite
      case Failure(cause) =>
        Console.err.println("error: unable to initialize benchmark suite")
        printCauseChain(cause, Console.err)
        sys.exit(1)
    }

    // Load information about available benchmarks.
    val realBenchmarks = suite.getMatchingBenchmarks(benchmarkIsReal).asScala

    if (config.printList) {
      print(formatBenchmarkList(suite, realBenchmarks))
    } else if (config.printRawList) {
      val listedBenchmarks =
        if (config.checkJvm) realBenchmarks.filter(suite.isBenchmarkCompatible)
        else realBenchmarks
      print(formatRawBenchmarkList(listedBenchmarks))
    } else if (config.printGroupList) {
      print(formatGroupList(realBenchmarks))
    } else if (config.benchmarkSpecifiers.isEmpty) {
      print(parser.usage())
    } else if (config.extractOnly) {
      // Extract selected benchmarks to individual directories.
      val benchmarks = selectBenchmarks(suite, config.benchmarkSpecifiers)
      extractBenchmarks(suite, benchmarks, config.extractBase)
    } else {
      // Collect specified benchmarks compatible with the JVM.
      var benchmarks = selectBenchmarks(suite, config.benchmarkSpecifiers)
      if (config.checkJvm) {
        benchmarks = excludeIncompatible(suite, benchmarks)
      }

      // Load all plugins in given order (including external policy).
      val externalPlugins = for ((specifier, args) <- config.pluginsWithArgs) yield {
        specifier -> createPlugin(suite, specifier, args)
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
      runBenchmarks(suite, benchmarks, policy, dispatcher)
    }
  }

  private def printCauseChain(initialCause: Throwable, output: PrintStream): Unit = {
    var cause = initialCause
    while (cause != null) {
      output.println(s"cause: ${initialCause.getMessage}")
      cause = cause.getCause
    }
  }

  private def extractBenchmarks(
    suite: BenchmarkSuite,
    benchmarks: Seq[BenchmarkDescriptor],
    extractBase: Path
  ): Unit = {
    // Strip companion object suffix from class name.
    val mainClass = RenaissanceSuite.getClass.getName.stripSuffix("$")

    for (descriptor <- benchmarks) {
      try {
        val extractDir = Files.createDirectories(extractBase.resolve(descriptor.name()))
        suite.extractBenchmark(mainClass, descriptor, extractDir)
      } catch {
        case ioe: IOException =>
          Console.err.println(
            s"Failed to extract benchmark '${descriptor.name()}': ${ioe.getMessage}"
          )
      }
    }
  }

  private def runBenchmarks(
    suite: BenchmarkSuite,
    benchmarks: Seq[BenchmarkDescriptor],
    policy: ExecutionPolicy,
    dispatcher: EventDispatcher
  ): Unit = {
    // TODO: Why collect failing benchmarks instead of just quitting whenever one fails?
    val failedBenchmarks = mutable.Buffer[BenchmarkDescriptor]()

    val vmStartNanos = getVmStartNanos

    // Notify observers that the suite is set up.
    dispatcher.notifyAfterHarnessInit()

    try {
      for (descriptor <- benchmarks) {
        val driver = ExecutionDriver.create(suite, descriptor, dispatcher, policy, vmStartNanos)

        try {
          driver.executeBenchmark()

        } catch {
          case t: Throwable =>
            // Notify observers that a benchmark failed.
            dispatcher.notifyOnBenchmarkFailure(descriptor.name)
            failedBenchmarks += descriptor

            t match {
              case _: ValidationException =>
                Console.err.println(
                  s"Benchmark '${descriptor.name()}' failed result validation:\n${t.getMessage}"
                )

              case _ =>
                Console.err.println(s"Benchmark '${descriptor.name()}' failed with exception:")
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
    suite: BenchmarkSuite,
    specifiers: Seq[String]
  ): Seq[BenchmarkDescriptor] = {
    val result = new mutable.LinkedHashSet[BenchmarkDescriptor]
    for (specifier <- specifiers) {
      if (suite.hasBenchmark(specifier)) {
        // Add an individual benchmark.
        result += suite.getBenchmark(specifier)
      } else if (suite.hasGroup(specifier)) {
        // Add benchmarks from the given group.
        result ++= suite.getGroupBenchmarks(specifier).asScala
      } else if (specifier == "all") {
        // Add all benchmarks except the dummy ones.
        result ++= suite.getMatchingBenchmarks(benchmarkIsReal).asScala
      } else {
        Console.err.println(s"Benchmark (or group) '$specifier' does not exist.")
        sys.exit(1)
      }
    }

    result.toSeq
  }

  private def excludeIncompatible(
    suite: BenchmarkSuite,
    benchmarks: Seq[BenchmarkDescriptor]
  ): Seq[BenchmarkDescriptor] = {
    def versionRange(b: BenchmarkDescriptor) = {
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

    // Exclude incompatible benchmarks with a warning.
    benchmarks
      .filter(b => {
        val isCompatible = suite.isBenchmarkCompatible(b)
        if (!isCompatible) {
          Console.err.println(
            s"Benchmark '${b.name()}' excluded: requires JVM version ${versionRange(b)} (found ${jvmSpecVersion()})."
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

  private def createPlugin[T](
    suite: BenchmarkSuite,
    specifier: String,
    args: mutable.Seq[String]
  ) = {
    def exitWithError(message: String) = {
      Console.err.println(s"Error: failed to load plugin '$specifier': $message")
      sys.exit(1)
    }

    // Only take the last '!' as a class name separator.
    val splitIndex = specifier.lastIndexOf("!")

    val className = specifier.substring(splitIndex + 1)

    val classPathString =
      if (splitIndex == -1) specifier else specifier.substring(0, splitIndex)
    val classPath = classPathString.split(File.pathSeparator).map(Paths.get(_)).toList
    classPath.filterNot(Files.isReadable).foreach { path =>
      exitWithError(s"'$path' does not exist or is not readable")
    }

    try {
      if (splitIndex != -1) {
        suite.createExtension(
          classPath.asJava,
          className,
          classOf[Plugin],
          args.toArray[String]
        )
      } else {
        suite.createDescribedExtension(
          classPath.asJava,
          "Renaissance-Plugin",
          classOf[Plugin],
          args.toArray[String]
        )
      }
    } catch {
      case e: ExtensionException => exitWithError(e.getMessage)
    }
  }

  private def getPolicy(
    config: Config,
    benchmarks: Seq[BenchmarkDescriptor],
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
    val result = mutable.Buffer[String]()
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

  private def formatRawBenchmarkList(benchmarks: Seq[BenchmarkDescriptor]) =
    benchmarks.map(_.name() + "\n").mkString

  private def formatBenchmarkList(
    suite: BenchmarkSuite,
    benchmarks: Seq[BenchmarkDescriptor]
  ) = {
    val indent = "    "

    val result = new StringBuilder
    for (bench <- benchmarks) {
      result.append(bench.name)
      if (!suite.isBenchmarkCompatible(bench)) {
        result.append(s" (not compatible with this JVM)")
      }
      result.append("\n")

      val summaryWords = bench.summary().split("\\s+")
      result.append(foldText(summaryWords, 65, indent).mkString("\n")).append("\n")

      bench
        .jvmVersionMin()
        .ifPresent(v => {
          result.append(s"${indent}Minimum JVM version required: $v")
          if (jvmSpecVersion().compareTo(v) < 0) {
            result.append(s" (found ${jvmSpecVersion()})")
          }
          result.append("\n")
        })

      bench
        .jvmVersionMax()
        .ifPresent(v => {
          result.append(s"${indent}Maximum JVM version supported: $v")
          if (jvmSpecVersion().compareTo(v) > 0) {
            result.append(s" (found ${jvmSpecVersion()})")
          }
          result.append("\n")
        })

      result.append(s"${indent}Default repetitions: ${bench.repetitions}").append("\n")
      result.append("\n")
    }

    result.toString
  }

  private def formatGroupList(benchmarks: Seq[BenchmarkDescriptor]) =
    benchmarks.flatMap(_.groups().asScala).distinct.sorted.map(_ + "\n").mkString

  private def benchmarkIsReal(benchmark: BenchmarkDescriptor) = {
    !benchmark.groups().contains("dummy")
  }

}
