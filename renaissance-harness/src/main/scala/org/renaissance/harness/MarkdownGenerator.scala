package org.renaissance.harness

import org.renaissance.Benchmark
import org.renaissance.BenchmarkContext
import org.renaissance.BenchmarkResult
import org.renaissance.Plugin
import org.renaissance.Plugin._
import org.renaissance.core.BenchmarkDescriptor
import org.renaissance.core.BenchmarkRegistry
import org.renaissance.core.Launcher
import org.renaissance.core.ModuleLoader
import scopt.OptionParser

import java.io.File
import java.io.IOException
import java.io.PrintWriter
import java.nio.charset.StandardCharsets
import java.util.function.Predicate
import scala.collection.SortedMap
import scala.collection.mutable
import scala.jdk.CollectionConverters._
import scala.util.Failure
import scala.util.Success
import scala.util.Try

/**
 * Generates README.md and CONTRIBUTING.md files for the suite.
 * This is currently part of the harness because is relies on
 * Scala string interpolation and collects information from
 * several (harness-internal) places.
 */
object MarkdownGenerator {

  private final class LocalConfig {
    var metadata: File = _

    val tags: mutable.Map[String, String] = mutable.Map()

    def setTag(key: String, value: String): LocalConfig = {
      tags.put(key, value)
      this
    }

    def setMetadata(path: String): LocalConfig = {
      this.metadata = new File(path)
      this
    }
  }

  def main(args: Array[String]): Unit = {
    val config = parseArgs(args)
    val benchmarks = createRegistry(config.metadata)
    val tags = initTagValues(benchmarks, config.tags)

    writeFile(() => formatReadme(tags), "README.md")
    writeFile(() => formatContribution(tags), "CONTRIBUTING.md")
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
      opt[String]('m', "metadata")
        .text("Sets the path to the property file with benchmark metadata.")
        .action((path, c) => c.setMetadata(path))
    }

    parser.parse(args, new LocalConfig) match {
      case Some(config) => config
      case None => sys.exit(1)
    }
  }

  private def createRegistry(metadata: File) = {
    var provider = Try(BenchmarkRegistry.createFromProperties(metadata))
    if (metadata == null) {
      provider = Try(BenchmarkRegistry.create())
    }

    provider match {
      case Success(registry) => registry
      case Failure(exception) =>
        Console.err.println("error: " + exception.getMessage)
        Console.err.println("error: failed to initialize benchmark registry")
        sys.exit(1)
    }
  }

  private def initTagValues(
    benchmarks: BenchmarkRegistry,
    tags: mutable.Map[String, String]
  ) = {
    val githubUrl = "https://github.com/renaissance-benchmarks/renaissance/"
    tags("logoUrl") = githubUrl + "raw/master/website/resources/images/mona-lisa-round.png"
    tags("codeOfConductUrl") = githubUrl + "blob/master/CODE-OF-CONDUCT.md"

    tags("jmhTargetPath") = "renaissance-jmh/target/scala-2.12"
    tags("jmhJarPrefix") = "renaissance-jmh-assembly"

    def selectBenchmarks(filter: Predicate[BenchmarkDescriptor]) = {
      benchmarks.getMatchingBenchmarks(filter).asScala.toSeq
    }

    // Don't list dummy benchmarks in the benchmark table to reduce clutter.
    val realBenchmarks = selectBenchmarks(!_.groups().contains("dummy"))
    tags("benchmarksList") = formatBenchmarkListMarkdown(realBenchmarks)
    tags("benchmarksTable") = formatBenchmarkTableMarkdown(realBenchmarks)

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

    val exampleBenchmarkClass = "MyJavaBenchmark"
    tags("exampleBenchmarkClass") = exampleBenchmarkClass
    tags("exampleBenchmarkName") = "my-java-benchmark"

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
      s"- `${b.name}` - ${b.summary} (default repetitions: ${b.repetitions})"
    }

    val result = new StringBuffer
    SortedMap.from(benchmarks.sortBy(_.name()).groupBy(_.primaryGroup()).toSeq).foreach {
      entry =>
        {
          val (group, benches) = entry
          result.append(s"#### $group").append("\n\n")
          result.append(benches.map(formatItem).mkString("\n\n")).append("\n\n")
        }
    }

    result.toString
  }

  private def formatBenchmarkTableMarkdown(benchmarks: Seq[BenchmarkDescriptor]) = {
    def formatRow(b: BenchmarkDescriptor) = {
      s"| ${b.name} | ${b.licenses.asScala.mkString(", ")} | ${b.distro} " +
        s"| ${b.jvmVersionMin.map[String](_.toString).orElse("")} " +
        s"| ${b.jvmVersionMax.map[String](_.toString).orElse("")} |"
    }

    // Don't list dummy benchmarks in the benchmark table to reduce clutter.
    benchmarks
      .sortBy(_.name())
      .map(formatRow)
      .mkString("\n")
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

To run a Renaissance benchmark, you need to have a JRE installed.
This allows you to execute the following `java` command:


```
$$ java -jar 'renaissance-gpl-${tags("renaissanceVersion")}.jar' <benchmarks>
```

Above, `<benchmarks>` is the list of benchmarks that you wish to run.
For example, you can specify `scala-kmeans` as the benchmark.

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


#### Complete list of command-line options

The following is a complete list of command-line options.

```
${tags("harnessUsage")}
```


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


### JMH support

You can also build and run Renaissance with JMH. To build a JMH-enabled JAR, run:

```
$$ tools/sbt/bin/sbt renaissanceJmh/jmh:assembly
```

To run the benchmarks using JMH, you can execute the following `java` command:

```
$$ java -jar '${tags("jmhTargetPath")}/${tags("jmhJarPrefix")}-${tags("renaissanceVersion")}.jar'
```


### Contributing

Please see the [contribution guide](CONTRIBUTING.md) for a description of the contribution process.


### Licensing

The Renaissance Suite comes in two distributions,
and is available under both the MIT license and the GPL3 license.
The GPL distribution with all the benchmarks is licensed under the GPL3 license,
while the MIT distribution includes only those benchmarks that themselves
have less restrictive licenses.

Depending on your needs, you can use either of the two distributions.
The following table contains the licensing information (and JVM version
requirements) for all the benchmarks:

| Benchmark        | Licenses   | Distro | JVM required (min) | JVM supported (max) |
| :--------------- | :--------- | :----: | :----------------: | :-----------------: |
${tags("benchmarksTable")}


### Documentation

Apart from documentation embedded directly in the source code, further
information about design and internals of the suite can be found in the
`documentation` folder of this project.

"""
  }

  def formatContribution(tags: Map[String, String]): String = {

    s"""
## Contribution Guide

### Building the suite

To build the suite and create the so-called fat JAR (or super JAR), you only
need to run `sbt` build tool as follows:

```
$$ tools/sbt/bin/sbt assembly
```

This will retrieve all the dependencies, compile all the benchmark projects and the harness,
bundle the JARs and create the final JAR under the `target` directory.


### Code organization and internals

The code is organized into three main parts:

- `renaissance-core`: these are the core APIs that a benchmark needs to work with,
  such as the runtime configuration, the benchmark base class or the policy.
- `renaissance-harness`: this is the overall suite project, which is responsible for
  parsing the arguments, loading the classes, and running the benchmark.
- a set of projects in the `benchmarks` directory: these are the individual groups of benchmarks
  that share a common set of dependencies. A group is typically thematic, relating to
  a particular framework or a JVM language, and benchmarks in different groups depend
  on a different set of libraries, or even the same libraries with different versions.
  The bundling mechanism of the suite takes care that the dependencies of the different groups
  never clash with each other.


### Adding a new benchmark

To add a new benchmark to an existing group, identify the respective project
in the `benchmarks` directory, and add a new top-level Scala (Java) class
that extends (implements) the `${tags("benchmarkClass")}` interface.

Here is an example:

```scala
import org.renaissance._
import org.renaissance.Benchmark._

@Summary("Runs some performance-critical Java code.")
final class ${tags("exampleBenchmarkClass")} extends ${tags("benchmarkClass")} {
  override def run(context: ${tags("contextClass")}): ${tags("benchmarkResultClass")} = {
    // This is the benchmark body, which in this case calls some Java code.
    JavaCode.runSomeJavaCode()
    // Return object for later validation of the operation result.
    return new ${tags("exampleBenchmarkClass")}Result()
  }
}
```

Above, the name of the benchmark will be automatically generated from the class name.
In this case, the name will be `${tags("exampleBenchmarkName")}`.

To create a new group of benchmarks (for example, benchmarks that depend on a new framework),
create an additional `sbt` project in the `benchmarks` directory,
using an existing project, such as `scala-stdlib`, as an example.
The project will be automatically picked up by the build system
and included into the Renaissance distribution.

Once the benchmark has been added, one needs to make sure to be compliant with the code
formatting of the project (rules defined in `.scalafmt.conf`).
A convenient sbt task can do that check:
```
$$ tools/sbt/bin/sbt renaissanceFormatCheck
```

Another one can directly update the source files to match the desired format:
```
$$ tools/sbt/bin/sbt renaissanceFormat
```

Moreover, the contents of the `README.md` and `CONTRIBUTING.md` files are automatically generated
from the codebase. Updating those files can be done with the `--readme` command-line flag.
Using sbt, one would do:
```
$$ tools/sbt/bin/sbt runMain ${tags("launcherClassFull")} --readme
```

### IDE development

#### IntelliJ

In order to work on the project with IntelliJ, one needs to install the following plugins :
  - `Scala` : part of the codebase uses Scala and Renaissance is organized in sbt projects.
  - `scalafmt` (optional) : adds an action that can be triggered with `Code -> Reformat with scalafmt`
  which will reformat the code according to the formatting rule defined in `.scalafmt.conf`
  (same as the `renaissanceFormat` sbt task).

Then, the root of this repository can be opened as an IntelliJ project.

### Benchmark evaluation and release process

In the open-source spirit, anyone can propose an additional benchmark by opening a pull request.
The code is then inspected by the community -- typically, the suite maintainers are involved
in the review, but anybody else is free join the discussion.
During the discussion, the reviewers suggest the ways in which
the benchmark could be improved.

Before submitting a pull request, it is recommendable to open an issue first,
and discuss the benchmark proposal with the maintainers.


#### Benchmark criteria

Here is some of the quality criteria that a new benchmark should satisfy:

- *Stylistically conformant*: the benchmark code must conform to existing formatting
  and stylistic standards in the suite.
- *Meaningful*: it must represent a meaningful workload that is either frequently executed,
  or it consists of code patterns and coding styles that are desired or arguably preferable,
  or it encodes some important algorithm, a data structure or a framework,
  or is significant in some other important way.
  If the benchmark is automatically generated by some tool,
  then it must be accompanied with a detailed explanation of why the workload is useful.
- *Observable*: it must constitute a run that is observable and measurable. For example,
  the run should last sufficiently long so that it is possible to accurately measure
  its running time, gather profiling information or observe a performance effect.
  Typically, this means that the benchmark duration should be between 0.5 and 10 seconds.
- *Deterministic*: the performance effects of the benchmark should be reproducible.
  Even if the benchmark consists of, for example, concurrent code that is inherently
  non-deterministic, the benchmark should behave relatively deterministically in terms
  of the number of threads that it creates, the objects it allocates, and the total amount
  of computation that it needs to do. For example, each of the benchmark repetitions should have
  a relatively stable running time on major JVMs.
- *New*: it must contain some new functionality that is not yet reflected in any of the existing
  benchmarks. If there is significant overlap with an existing benchmark, then it should be
  explained why the new benchmark is necessary.
- *Self-contained*: it must be runnable within a single JVM instance, without any additional
  software installation, operating system functionality, operating system services,
  other running processes, online services, networked deployments or similar.
  The JVM installation should be sufficient to run all the code of the benchmark.
  For example, if the benchmark is exercising Apache Spark, then the workers should run
  in the local mode, and if the benchmark targets a database, then it should be embedded.
  The benefit is that the performance effects of the benchmark are easy to measure,
  and the code is reproducible everywhere.
- *Open-source*: the benchmark must consist of open-source code, with well-defined licenses.


#### Code of Conduct

We would also like to point you to the
[Renaissance Code of Conduct](${tags("codeOfConductUrl")}). As a member
of the Renaissance community, make sure that you follow it to guarantee an enjoyable experience for every member of
the community.

#### Release process

While the open-source process is designed to accept contributions on an ongoing basis,
we expect that this benchmark suite will grow considerably over the course of time.
We will therefore regularly release snapshots of this suite, which will be readily available.
These will be known as *minor releases*.

Although we will strive to have high-quality, meaningful benchmarks, it will be necessary
to proliferate the most important ones, and publish them as *major releases*.
This way, researchers and developers will be able to test their software
against those benchmarks that were deemed most relevant.
A major release will still include all the benchmarks in the suite, but the list of highlighted
benchmarks might evolve between major releases.

Once a year, a committee convenes and discusses which important benchmarks were contributed
since the last release, and should become highlighted in the next major release.
The committee consists of members from various universities and companies,
who are involved in research and development in virtual machine, compiler, memory management,
static and dynamic analysis, and performance engineering.

The committee goes over the benchmark list, and inspect the new ones since the last release.
The members can recommend specific benchmarks for inclusion in the highlighted list,
and can present their arguments about why those benchmarks should be included.
In addition, the members can recommend the exclusion of some benchmarks.
The committee members then vote, and the majority is the basis for a decision.

The new major release is then bundled and the binaries are made available publicly.

The current members of the committee are:

- Walter Binder, Universita della Svizzera italiana
- Steve Blackburn, Australian National University
- Lubomir Bulej, Charles University
- Gilles Duboscq, Oracle Labs
- Francois Farquet, Oracle Labs
- Vojtech Horky, Charles University
- David Leopoldseder, Johannes Kepler University Linz
- Guillaume Martres, Ecole Polytechnique Federale de Lausanne
- Aleksandar Prokopec, Oracle Labs
- Andrea Rosa, Universita della Svizzera italiana
- Denys Shabalin, Ecole Polytechnique Federale de Lausanne
- Petr Tuma, Charles University
- Alex Villazon, Universidad Privada Boliviana
"""
  }
}
