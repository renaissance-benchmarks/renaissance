package org.renaissance

import java.io.File
import java.io.IOException
import java.io.PrintWriter
import java.nio.charset.StandardCharsets

import org.renaissance.harness.ExecutionPolicy
import org.renaissance.harness.Plugin
import org.renaissance.harness.Plugin._
import org.renaissance.util.BenchmarkInfo
import org.renaissance.util.BenchmarkRegistry
import org.renaissance.util.ModuleLoader
import scopt.OptionParser

import scala.collection.JavaConverters._
import scala.collection.mutable
import scala.util.Failure
import scala.util.Success
import scala.util.Try

/**
 * Generates README.md and CONTRIBUTION.md files for the suite.
 * This is currently part of the harness because is relies on
 * Scala string interpolation and collects information from
 * several (harness-internal) places.
 */
object MarkdownGenerator {

  private final class LocalConfig {
    var metadata: File = null

    val tags = {
      val benchmarkPkg = classOf[Benchmark].getPackage
      mutable.Map[String, String](
        "renaissanceTitle" -> benchmarkPkg.getImplementationTitle,
        "renaissanceVersion" -> benchmarkPkg.getImplementationVersion
      )
    }

    def setTag(key: String, value: String) = {
      tags.put(key, value)
      this
    }

    def setMetadata(path: String) = {
      this.metadata = new File(path)
      this
    }
  }

  def main(args: Array[String]): Unit = {
    val config = parseArgs(args)
    val benchmarks = createRegistry(config.metadata)
    val tags = initTagValues(benchmarks, config.tags)

    writeFile(() => formatReadme(tags), "README.md")
    writeFile(() => formatContribution(tags), "CONTRIBUTION.md")
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
      case None         => sys.exit(1)
    }
  }

  private def createRegistry(metadata: File) = {
    var provider = Try(BenchmarkRegistry.createFromProperties(metadata))
    if (metadata == null) {
      provider = Try(BenchmarkRegistry.createDefault())
    }

    provider match {
      case Success(registry) => registry
      case Failure(exception) => {
        Console.err.println("error: " + exception.getMessage)
        Console.err.println("error: failed to initialize benchmark registry")
        sys.exit(1)
      }
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

    tags("benchmarksList") = formatBenchmarkListMarkdown(benchmarks)
    tags("benchmarksTable") = formatBenchmarkTableMarkdown(benchmarks)
    tags("benchmarkClass") = classOf[Benchmark].getSimpleName
    tags("benchmarkResultClass") = classOf[BenchmarkResult].getSimpleName

    tags("configClass") = classOf[Config].getSimpleName
    tags("pluginClass") = classOf[Plugin].getSimpleName
    tags("policyClass") = classOf[ExecutionPolicy].getSimpleName

    tags("harnessInitListenerClass") = classOf[HarnessInitListener].getSimpleName
    tags("harnessShutdownListenerClass") = classOf[HarnessShutdownListener].getSimpleName
    tags("benchmarkSetUpListenerClass") = classOf[BenchmarkSetUpListener].getSimpleName
    tags("benchmarkTearDownListenerClass") = classOf[BenchmarkTearDownListener].getSimpleName
    tags("benchmarkResultListenerClass") = classOf[BenchmarkResultListener].getSimpleName
    tags("benchmarkFailureListenerClass") = classOf[BenchmarkFailureListener].getSimpleName
    tags("operationSetUpListenerClass") = classOf[OperationSetUpListener].getSimpleName
    tags("operationTearDownListenerClass") = classOf[OperationTearDownListener].getSimpleName

    tags("launcherClassFull") = classOf[Launcher].getName
    tags("moduleLoaderClass") = classOf[ModuleLoader].getSimpleName

    val harnessConfigParser = new ConfigParser(tags.toMap)
    tags("harnessUsage") = harnessConfigParser.usage

    val exampleBenchmarkClass = "MyJavaBenchmark"
    tags("exampleBenchmarkClass") = exampleBenchmarkClass
    tags("exampleBenchmarkName") = "my-java-benchmark"

    tags.toMap
  }

  private def writeFile(supplier: () => String, file: String) = {
    val value = Try(supplier()) match {
      case Success(value) => value
      case Failure(exception) => {
        Console.err.println("error: " + exception.getMessage)
        Console.err.println("error: failed to format " + file)
        sys.exit(1)
      }
    }

    try {
      val writer = new PrintWriter(file, StandardCharsets.UTF_8.name)

      try {
        writer.write(value)
        println(file + " updated.");

      } finally {
        writer.close()
      }
    } catch {
      case exception: IOException => {
        Console.err.println("error: " + exception.getMessage)
        Console.err.println("error: failed to write " + file)
        sys.exit(1)
      }
    }
  }

  private def formatBenchmarkListMarkdown(benchmarks: BenchmarkRegistry) = {
    def formatItem(b: BenchmarkInfo) = {
      s"- `${b.name}` - ${b.summary} (default repetitions: ${b.repetitions})"
    }

    val result = new StringBuffer
    for ((group, benches) <- benchmarks.byGroup().asScala) {
      result.append(s"#### ${group}").append("\n\n")
      result.append(benches.asScala.map(formatItem(_)).mkString("\n\n")).append("\n\n")
    }

    result.toString
  }

  private def formatBenchmarkTableMarkdown(benchmarks: BenchmarkRegistry) = {
    def formatRow(b: BenchmarkInfo) = {
      s"| ${b.name} | ${b.printableLicenses} | ${b.distro} |"
    }

    benchmarks.getAll().asScala.map(formatRow(_)).mkString("\n")
  }

  def formatReadme(tags: Map[String, String]): String = {
    return s"""

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


### Building the suite

To build the suite and create the so-called fat JAR (or super JAR), you only
need to run `sbt` built tool:

```
$$ tools/sbt/bin/sbt assembly
```

This will retrieve all the dependencies, compile all the benchmark projects and the harness,
bundle the JARs and create the final JAR under `target` directory.


### Running the benchmarks

To run a Renaissance benchmark, you need to have a JRE installed.
This allows you to execute the following `java` command:

```
$$ java -jar '<renaissance-home>/target/renaissance-gpl-${tags("renaissanceVersion")}.jar' <benchmarks>
```

Above, the `<renaissance-home>` is the path to the root directory of the Renaissance distribution,
and `<benchmarks>` is the list of benchmarks that you wish to run.
For example, you can specify `scala-kmeans` as the benchmark.


#### Complete list of command-line options

The following is a complete list of command-line options.

```
${tags("harnessUsage")}
```


### List of benchmarks

The following is the complete list of benchmarks, separated into groups.

${tags("benchmarksList")}


### Execution policies

The suite generally executes the measured operation of a benchmark multiple times
and uses an execution policy to determine how many time to repeat the execution.
By default, the suite supports executing the operation a fixed number of times
and a fixed amount of time. These policies are implicitly selected by setting
the number of iterations or the execution time on the suite command line.

To provide additional control over execution of the measured operation, the
suite also allows to specify a custom execution policy, which has to implement
the ${tags("policyClass")} interface.


### Plugins and interfacing with external tools

If you are using an external tool to inspect a benchmark, such as an instrumentation agent,
or a profiler, then you will need to make this tool aware of when a benchmark iteration
is starting and when it is ending.
To allow this, the suite allows specifying custom plugins, which are notified when necessary.
Such a plugin needs to implement the `${tags("pluginClass")}` marker interface as well as
interfaces from the `${tags("pluginClass")}` interface name space which indicate the events
a plugin is interested in.

Here is an example of a simple plugin:

```
class MyPlugin extends ${tags("pluginClass")} with ${tags("harnessInitListenerClass")} {
  override def afterHarnessInit() = {
    // Initialize the plugin after the harness finished initializing
  }

  override def beforeOperation(index: Int, benchmark: String) = {
    // Notify the tool that the measured operation is about to start.
  }

  override def afterOperation(index: Int, benchmark: String) = {
    // Notify the tool that the measured operations has finished.
  }
}
```

The currently supported events are represented by the following interfaces:
- `${tags("harnessInitListenerClass")}`
- `${tags("harnessShutdownListenerClass")}`
- `${tags("benchmarkSetUpListenerClass")}`
- `${tags("benchmarkTearDownListenerClass")}`
- `${tags("benchmarkResultListenerClass")}`
- `${tags("benchmarkFailureListenerClass")}`
- `${tags("operationSetUpListenerClass")}`
- `${tags("operationTearDownListenerClass")}`

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

Please see the [CONTRIBUTION](CONTRIBUTION.md) page for a description of the contributing process.

### Licensing

The Renaissance Suite comes in two distributions,
and is available under both the MIT license and the GPL3 license.
The GPL distribution with all the benchmarks is licensed under the GPL3 license,
while the MIT distribution includes only those benchmarks that themselves
have less restrictive licenses.

Depending on your needs, you can use either of the two distributions.
The following table contains the licensing information of all the benchmarks:

| Benchmark     | Licenses      | Renaissance Distro |
| ------------- | ------------- |:------------------:|
${tags("benchmarksTable")}


### Design overview

The Renaissance benchmark suite is organized into several `sbt` projects:

- the `renaissance-core` folder that contains a set of *core* classes
  (common interfaces and a harness launcher)
- the `renaissance-harness` folder that contains the actual harness
- the `benchmarks` folder contains a set of *subprojects*, each containing a set of benchmarks
  for a specific domain (and having a separate set of dependencies)

The *core* project is written in pure Java, and it contains the basic benchmark API.
Its most important elements are the `${tags("benchmarkClass")}` interface,
which must be implemented by each benchmark, and the annotations in the
`${tags("benchmarkClass")}` interface name space, which are used to provide
benchmark meta data, such as a summary or a detailed description.
Consequently, each *subproject* depends on the *core* project.

Classes from the *core* are loaded (when Renaissance is started) by the default
classloader. Classes from other projects (including the harness and individual benchmarks)
are loaded by separate classloaders. This separation helps ensure that there
are no clashes between dependencies of different projects (each benchmark may
depend on different versions of external libraries).

The *harness* project implements the functionality that is necessary
to parse the input arguments, to run the benchmarks, to generate documentation,
and so on. The *harness* is written in Scala and is loaded by the *core*
in a separate classloader to ensure clean environment for running the
benchmarks.

The JARs of the subprojects (benchmarks and harness) are copied as generated
*resources* and embedded into the resulting JAR artifact.

```
renaissance-core
  ^
  | (classpath dependencies)
  |
  |-- renaissance harness
  |
  |-- benchmark one
  | `-- dependencies for benchmark one
  |
  |-- ...
  |
  `-- benchmark n
```

When the harness is started, it uses the input arguments to select the benchmark,
and then unpacks the JARs of the corresponding benchmark group into a scratch folder.
The harness then creates a classloader with the unpacked JARs and loads the benchmark group.
The class loader is created directly below the default class loader. Because
the default class loader contains only base JRE classes and common interfaces
of *core*, it ensures that dependencies of a benchmark are never mixed with any
dependencies of any other benchmark or the harness.

```
        boot class loader (JDK)
                   ^
                   |
          system class loader
                (core)
         ^                   ^
         |                   |
  URL class loader    URL class loader
     (harness)          (benchmark)
```

We need to do this to, e.g., avoid accidentally resolving the wrong class
by going through the system class loader (this can easily happen with,
e.g. Apache Spark and Scala, due to the way that Spark internally resolves some classes).

You can see the further details of the build system in the top-level `build.sbt` file,
in the `renaissance-suite.scala` file and in `${tags("moduleLoaderClass")}`.


"""
  }

  def formatContribution(tags: Map[String, String]): String = {

    return s"""

## Contribution Guide

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

```
import org.renaissance._
import org.renaissance.Benchmark._

@Summary("Runs some performance-critical Java code.")
final class ${tags("exampleBenchmarkClass")} extends ${tags("benchmarkClass")} {
  override def runIteration(config: ${tags("configClass")}): ${tags(
      "benchmarkResultClass"
    )} = {
    // This is the benchmark body, which in this case calls some Java code.
    JavaCode.runSomeJavaCode()
    // Return object for later validation of the iteration.
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

Moreover, the contents of the README and CONTRIBUTION files are automatically generated from the codebase.
Updating those files can be done with the `--readme` command-line flag. Using sbt, one would do:
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
