package org.renaissance.harness

import org.renaissance.Benchmark
import org.renaissance.BenchmarkContext
import org.renaissance.BenchmarkResult
import org.renaissance.Plugin
import org.renaissance.Plugin._
import org.renaissance.core.BenchmarkDescriptor
import org.renaissance.core.BenchmarkSuite
import org.renaissance.core.Launcher
import org.renaissance.core.ModuleLoader
import scopt.OptionParser

import java.io.IOException
import java.io.PrintWriter
import java.net.URI
import java.nio.charset.StandardCharsets
import java.nio.file.Paths
import java.util.Collections
import java.util.Optional
import java.util.function.Predicate
import scala.collection.mutable
import scala.jdk.CollectionConverters._
import scala.util.Failure
import scala.util.Success
import scala.util.Try

/**
 * Generates README.md file for the suite.
 * This is currently part of the harness because is relies on
 * Scala string interpolation and collects information from
 * several (harness-internal) places.
 */
object MarkdownGenerator {

  private final class LocalConfig {
    var metadataUri: Optional[URI] = Optional.empty()

    val tags: mutable.Map[String, String] = mutable.Map()

    def setTag(key: String, value: String): LocalConfig = {
      tags.put(key, value)
      this
    }

    def setMetadataUri(uri: URI): LocalConfig = {
      metadataUri = Optional.of(uri)
      this
    }
  }

  def main(args: Array[String]): Unit = {
    val config = parseArgs(args)
    val benchmarks = createSuite(config.metadataUri)
    val tags = initTagValues(benchmarks, config.tags)

    writeFile(() => formatReadme(tags), "README.md")
  }

  private def parseArgs(args: Array[String]) = {
    val parser = new OptionParser[LocalConfig]("MarkdownGenerator") {
      head("Markdown documentation generator")
      opt[String]('t', "title")
        .text("Sets the Renaissance suite title.")
        .action((title, c) => c.setTag("renaissanceTitle", title))
      opt[String]('v', "version")
        .text("Sets the Renaissance suite version.")
        .action((version, c) => c.setTag("renaissanceVersion", version))
      opt[URI]('m', "metadata")
        .valueName("<uri>")
        .text("Sets the path to the property file with benchmark metadata.")
        .action((uri, c) => c.setMetadataUri(uri))
    }

    parser.parse(args, new LocalConfig) match {
      case Some(config) => config
      case None => sys.exit(1)
    }
  }

  private def createSuite(metadataOverrideUri: Optional[URI]) = {
    //
    // Create a benchmark suite with default benchmark metadata URI (unless
    // overridden), but with no parameter overrides and no module loader.
    //
    val provider = Try(
      BenchmarkSuite.create(
        Paths.get(""),
        "default",
        metadataOverrideUri,
        Collections.emptyMap(),
        false /* without module loader */
      )
    )

    provider match {
      case Success(registry) => registry
      case Failure(cause) =>
        Console.err.println("error: " + cause.getMessage)
        Console.err.println("error: failed to initialize benchmark registry")
        sys.exit(1)
    }
  }

  private def initTagValues(
    suite: BenchmarkSuite,
    tags: mutable.Map[String, String]
  ) = {
    val githubUrl = "https://github.com/renaissance-benchmarks/renaissance/"
    tags("logoUrl") = githubUrl + "raw/master/logo.png"
    tags("codeOfConductUrl") = githubUrl + "blob/master/CODE-OF-CONDUCT.md"

    tags("jmhTargetPath") = "renaissance-jmh/target"
    tags("jmhJarPrefix") = "renaissance-jmh"

    def selectBenchmarks(filter: Predicate[BenchmarkDescriptor]): Seq[BenchmarkDescriptor] = {
      suite.getMatchingBenchmarks(filter).asScala.toSeq
    }

    // Don't list dummy benchmarks in the benchmark table to reduce clutter.
    val realBenchmarks = selectBenchmarks(!_.groups().contains("dummy"))
    tags("benchmarksList") = formatBenchmarkListMarkdown(realBenchmarks)

    // List dummy benchmarks separately.
    val dummyBenchmarks = selectBenchmarks(_.groups().contains("dummy"))
    tags("dummyBenchmarksList") = formatBenchmarkListMarkdown(dummyBenchmarks)

    tags("benchmarkClass") = classOf[Benchmark].getSimpleName
    tags("benchmarkResultClass") = classOf[BenchmarkResult].getSimpleName

    tags("contextClass") = classOf[BenchmarkContext].getSimpleName
    tags("pluginClass") = classOf[Plugin].getSimpleName
    tags("policyClass") = classOf[ExecutionPolicy].getSimpleName

    tags("afterHarnessInitListenerClass") = classOf[AfterHarnessInitListener].getSimpleName
    tags("beforeHarnessShutdownListenerClass") =
      classOf[BeforeHarnessShutdownListener].getSimpleName

    tags("beforeBenchmarkSetUpListenerClass") =
      classOf[BeforeBenchmarkSetUpListener].getSimpleName
    tags("afterBenchmarkTearDownListenerClass") =
      classOf[AfterBenchmarkTearDownListener].getSimpleName

    tags("afterBenchmarkSetUpListenerClass") =
      classOf[AfterBenchmarkSetUpListener].getSimpleName
    tags("beforeBenchmarkTearDownListenerClass") =
      classOf[BeforeBenchmarkTearDownListener].getSimpleName

    tags("afterOperationSetUpListenerClass") =
      classOf[AfterOperationSetUpListener].getSimpleName
    tags("beforeOperationTearDownListenerClass") =
      classOf[BeforeOperationTearDownListener].getSimpleName

    tags("benchmarkFailureListenerClass") = classOf[BenchmarkFailureListener].getSimpleName
    tags("measurementResultListenerClass") = classOf[MeasurementResultListener].getSimpleName
    tags("measurementResultPublisherClass") = classOf[MeasurementResultPublisher].getSimpleName

    tags("launcherClassFull") = classOf[Launcher].getName
    tags("moduleLoaderClass") = classOf[ModuleLoader].getSimpleName
    tags("renaissanceSuiteClass") = "RenaissanceSuite"

    val harnessConfigParser = new ConfigParser(tags.toMap)
    tags("harnessUsage") = harnessConfigParser.usage()

    tags.toMap
  }

  private def writeFile(supplier: () => String, file: String): Unit = {
    val value = Try(supplier()) match {
      case Success(suppliedValue) => suppliedValue
      case Failure(exception) =>
        Console.err.println("error: " + exception.getMessage)
        Console.err.println("error: failed to format " + file)
        sys.exit(1)
    }

    try {
      val writer = new PrintWriter(file, StandardCharsets.UTF_8.name)

      try {
        writer.write(value)
        println(file + " updated.")

      } finally {
        writer.close()
      }
    } catch {
      case exception: IOException =>
        Console.err.println("error: " + exception.getMessage)
        Console.err.println("error: failed to write " + file)
        sys.exit(1)
    }
  }

  private def formatBenchmarkListMarkdown(benchmarks: Seq[BenchmarkDescriptor]) = {
    def formatItem(b: BenchmarkDescriptor) = {
      s"- `${b.name}` - ${b.summary}\n  \\\n  " +
        s"Default repetitions: ${b.repetitions}; " +
        s"${b.licenses.asScala.mkString(", ")} license, ${b.distro} distribution; " +
        s"Supported JVM: ${b.jvmVersionMin.map[String](_.toString).orElse("1.8")} " +
        s"${b.jvmVersionMax.map[String]("- " + _.toString).orElse("and later")}"
    }

    val result = new StringBuilder()
    val benchmarksByGroup = benchmarks.groupBy(_.primaryGroup())
    benchmarks.map(_.primaryGroup()).sorted.distinct.foreach { group =>
      val benches = benchmarksByGroup(group).sortBy(_.name())
      result.append(s"#### $group").append("\n\n")
      result.append(benches.map(formatItem).mkString("\n\n")).append("\n\n")
    }

    result.toString
  }

  def formatReadme(tags: Map[String, String]): String = {
    s"""
## Renaissance Benchmark Suite

<p align="center">
  <img height="180px" src="${tags("logoUrl")}"/>
</p>


The Renaissance Benchmark Suite aggregates common modern JVM workloads,
including, but not limited to, Big Data, machine-learning, and functional programming.
The suite is intended to be used to optimize just-in-time compilers, interpreters, GCs,
and for tools such as profilers, debuggers, or static analyzers, and even different hardware.
It is intended to be an open-source, collaborative project,
in which the community can propose and improve benchmark workloads.


### Running the suite

To run the suite, you will need to download a Renaissance Suite JAR
from <https://renaissance.dev/download>.
If you wish to build it yourself, please, consult [CONTRIBUTING.md](CONTRIBUTING.md)
for instructions on building.

To run a Renaissance benchmark, you need to have a JRE version 11 (or later)
installed and execute the following `java` command:

```
$$ java -jar 'renaissance-gpl-${tags("renaissanceVersion")}.jar' <benchmarks>
```

In the above command, `<benchmarks>` is the list of benchmarks that you want to run.
You can refer to individual benchmarks, e.g., `scala-kmeans`, or a group of benchmarks,
e.g., `apache-spark`.

The suite generally executes the benchmark's measured operation multiple times. By default,
the suite executes each benchmark operation for a specific number of times. The benchmark-specific
number of repetitions is only intended for quick visual evaluation of benchmark execution time,
but is not sufficient for thorough experimental evaluation, which will generally need much more
repetitions.

For thorough experimental evaluation, the benchmarks should be repeated for a large number of
times or executed for a long time. The number of repetitions and the execution time can be
set for all benchmarks using the `-r` or `-t` options. More fine-grained control over benchmark
execution can be achieved by providing the harness with a plugin implementing a custom execution
policy (see [below](#plugins) for details).


### Licensing

The Renaissance Suite comes in two distributions,
and is available under both the MIT license and the GPL3 license.
The GPL distribution with all the benchmarks is licensed under the GPL3 license,
while the MIT distribution includes only those benchmarks that themselves
have less restrictive licenses.

Depending on your needs, you can use either of the two distributions.

The list below contains the licensing information (and JVM version requirements)
for each benchmark.


### List of benchmarks

The following is the complete list of benchmarks, separated into groups.

${tags("benchmarksList")}

The suite also contains a group of benchmarks intended solely for testing
purposes:

${tags("dummyBenchmarksList")}

### <a name="plugins">Using plugins to customize the harness</a>

If you are using an external tool to inspect a benchmark, such as an instrumentation agent,
or a profiler, then you may need to make this tool aware of when a benchmark's measured
operation is about to be executed and when it finished executing.

If you need to collect additional metrics associated with the execution of the measured
operation, e.g., hardware counters, you will need to be notified about operation execution,
and you may want to store the measured values in the output files produced by the harness.

If you need the harness to produce output files in different format (other than CSV or JSON),
you will need to be notified about values of metrics collected by the harness and other plugins.

If you need more fine-grained control over the repetition of the benchmark's measured operation,
you will need to be able to tell the harness when to keep executing the benchmark and when to
stop.

To this end, the suite provides hooks for plugins which can subscribe to events related to
harness state and benchmark execution.

This repository contains two such plugins: one that uses a native agent built with
[PAPI](https://icl.utk.edu/papi/) to collect information from hardware counters and
a plugin for collecting information from a
[CompilationMXBean](https://docs.oracle.com/javase/8/docs/api/java/lang/management/CompilationMXBean.html).
See their respective READMEs under the `plugin` directory for more information.

If you wish to create your own plugin, please consult
[documentation/plugins.md](documentation/plugins.md) for more details.

To make the harness use an external plugin, it needs to be specified on the command line.
The harness can load multiple plugins, and each must be enabled using the
`--plugin <class-path>[!<class-name>]` option. The `<class-path>` is the class path on which
to look for the plugin class (optionally, you may add `<class-name>` to specify a fully
qualified name of the plugin class).

Custom execution policy must be enabled using the `--policy <class-path>!<class-name>` option.
The syntax is the same as in case of normal plugins (and the policy is also a plugin, which
can register for all event types), but this option tells the harness to actually use the
plugin to control benchmark execution. Other than that, policy is treated the same way as a
plugin.

When registering plugins for pair events (harness init/shutdown, benchmark set up/tear down,
operation set up/tear down), the plugins specified earlier will "wrap" plugins specified later.
This means that for example plugins that want to collect additional measurements and need to
invoked as close as possible to the measured operation need to be specified last. Note that
this also applies to an external execution policy, which would be generally specified first,
but any order is possible.

Plugins (and policies) can receive additional command line arguments. Each argument must be
given using the `--with-arg <arg>` option, which appends `<arg>` to the list of arguments for
the plugin (or policy) that was last mentioned on the command line. Whenever a `--plugin`
(or `--policy`) option is encountered, the subsequent `--with-arg` options will append
arguments to that plugin (or policy).


### Complete list of command-line options

The following is a complete list of command-line options.

```
${tags("harnessUsage")}
```


### JMH support

You can also build and run Renaissance with JMH. To build a JMH-enabled JAR, run:

```
$$ tools/sbt/bin/sbt renaissanceJmhPackage
```

To run the benchmarks using JMH, you can execute the following `java` command:

```
$$ java -jar '${tags("jmhTargetPath")}/${tags("jmhJarPrefix")}-${tags("renaissanceVersion")}.jar'
```


### Contributing

Please see the [contribution guide](CONTRIBUTING.md) for a description of the contribution process.


### Documentation

Apart from documentation embedded directly in the source code, further
information about design and internals of the suite can be found in the
`documentation` folder of this project.


### Support

When you find a bug in the suite, when you want to propose a new benchmark or
ask for help, please, open an [Issue](https://github.com/renaissance-benchmarks/renaissance/issues)
at the project page at GitHub.

"""
  }
}
