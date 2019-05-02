package org.renaissance

import java.io.File
import java.nio.charset.StandardCharsets
import org.apache.commons.io.FileUtils
import org.apache.commons.io.IOUtils
import scala.collection._
import scala.collection.JavaConverters._
import scopt._
import spray.json._
import spray.json.DefaultJsonProtocol._
import org.renaissance.util.ModuleLoader

object RenaissanceSuite {
  abstract class ResultWriter extends ResultObserver {
    val allResults = new mutable.HashMap[String, mutable.Map[String, mutable.ArrayBuffer[Long]]]

    def onNewResult(benchmark: String, metric: String, value: Long): Unit = {
      val benchStorage = allResults.getOrElse(benchmark, new mutable.HashMap)
      allResults.update(benchmark, benchStorage)
      val metricStorage = benchStorage.getOrElse(metric, new mutable.ArrayBuffer)
      benchStorage.update(metric, metricStorage)
      metricStorage += value
    }

    def getBenchmarks: Iterable[String] = {
      allResults.keys
    }

    def getColumns(): Seq[String] = {
      allResults.values.flatMap(_.keys).toSeq.distinct.sorted
    }

    def getResults()
      : Iterable[(String, Map[String, mutable.ArrayBuffer[Long]], Iterable[Int])] =
      for {
        benchName <- getBenchmarks
        benchResults = allResults(benchName)
        maxIndex = benchResults.values.map(_.size).max - 1
      } yield
        (
          benchName,
          benchResults.toMap.asInstanceOf[Map[String, mutable.ArrayBuffer[Long]]],
          (0 to maxIndex)
        )
  }

  class CsvWriter(val filename: String) extends ResultWriter {

    def onExit(): Unit = {
      val csv = new StringBuffer
      csv.append("benchmark")
      val columns = new mutable.ArrayBuffer[String]
      for (c <- getColumns) {
        columns += c
        csv.append(",").append(c)
      }
      csv.append("\n")

      for ((benchmark, results, repetitions) <- getResults) {
        for (i <- repetitions) {
          val line = new StringBuffer
          line.append(benchmark)
          for (c <- columns) {
            val values = results.getOrElse(c, new mutable.ArrayBuffer)
            val score = if (i < values.size) values(i).toString else "NA"
            line.append(",").append(score.toString)
          }
          csv.append(line).append("\n")
        }
      }

      FileUtils.write(
        new File(filename),
        csv.toString,
        java.nio.charset.StandardCharsets.UTF_8,
        false
      )
    }
  }

  class JsonWriter(val filename: String) extends ResultWriter {

    def getEnvironment(): JsValue = {
      val result = new mutable.HashMap[String, JsValue]

      val osInfo = new mutable.HashMap[String, JsValue]
      osInfo.update("name", System.getProperty("os.name", "unknown").toJson)
      osInfo.update("arch", System.getProperty("os.arch", "unknown").toJson)
      osInfo.update("version", System.getProperty("os.version", "unknown").toJson)
      result.update("os", osInfo.toMap.toJson)

      val runtimeMxBean = management.ManagementFactory.getRuntimeMXBean()
      val vmArgs = runtimeMxBean.getInputArguments()

      val vmInfo = new mutable.HashMap[String, JsValue]
      vmInfo.update("name", System.getProperty("java.vm.name", "unknown").toJson)
      vmInfo.update("vm_version", System.getProperty("java.vm.version", "unknown").toJson)
      vmInfo.update("jre_version", System.getProperty("java.version", "unknown").toJson)
      vmInfo.update("args", vmArgs.asScala.toList.toJson)
      result.update("vm", vmInfo.toMap.toJson)

      return result.toMap.toJson
    }

    def onExit(): Unit = {
      val columns = getColumns

      val tree = new mutable.HashMap[String, JsValue]
      tree.update("format_version", 1.toJson)
      tree.update("benchmarks", getBenchmarks.toList.toJson)
      tree.update("environment", getEnvironment)

      val resultTree = new mutable.HashMap[String, JsValue]
      for ((benchmark, results, repetitions) <- getResults) {
        val subtree = new mutable.ArrayBuffer[JsValue]
        for (i <- repetitions) {
          val scores = new mutable.HashMap[String, JsValue]
          for (c <- columns) {
            val values = results.getOrElse(c, new mutable.ArrayBuffer)
            if (i < values.size) {
              scores.update(c, values(i).toJson)
            }
          }
          subtree += scores.toMap.toJson
        }
        resultTree.update(benchmark, subtree.toList.toJson)
      }

      tree.update("results", resultTree.toMap.toJson)

      FileUtils.write(
        new File(filename),
        tree.toMap.toJson.prettyPrint,
        java.nio.charset.StandardCharsets.UTF_8,
        false
      )
    }
  }

  class BenchmarkMetaInformation(
    val name: String,
    val description: String,
    val defaultRepetitions: Int,
    val licenses: Array[String],
    val distro: String
  )

  val benchmarkGroups = {
    val map = new mutable.LinkedHashMap[String, String]
    val lines = IOUtils.lineIterator(
      getClass.getResourceAsStream("/benchmark-group.txt"),
      StandardCharsets.UTF_8
    )
    while (lines.hasNext) {
      val line = lines.next()
      val parts = line.split("=")
      map(parts(0)) = parts(1)
    }
    map
  }

  val groupBenchmarks =
    benchmarkGroups.groupBy({ case (_, group) => group }).mapValues(_.keys.toSeq)

  val benchmarks = benchmarkGroups.keys

  val benchmarkDetails = {
    val details = new mutable.HashMap[String, BenchmarkMetaInformation]
    val detailsAsProps = new java.util.Properties
    detailsAsProps.load(getClass.getResourceAsStream("/benchmark-details.properties"))
    for (name <- benchmarks) {
      val description = detailsAsProps.getProperty(
        "benchmark." + name + ".description",
        "Description not provided"
      )
      val repetitions = detailsAsProps.getProperty(
        "benchmark." + name + ".repetitions",
        "-1"
      )
      val licenses = detailsAsProps
        .getProperty(
          "benchmark." + name + ".licenses",
          "unknown"
        )
        .split(",")
      val distro = detailsAsProps.getProperty(
        "benchmark." + name + ".distro",
        "unknown"
      )
      details(name) =
        new BenchmarkMetaInformation(name, description, repetitions.toInt, licenses, distro)
    }
    details
  }

  val groupJars = {
    val map = new mutable.HashMap[String, List[String]]
    val lines = IOUtils.lineIterator(
      getClass.getResourceAsStream("/groups-jars.txt"),
      StandardCharsets.UTF_8
    )
    while (lines.hasNext) {
      val line = lines.next()
      val parts = line.split("=")
      val group = parts(0)
      val jars = parts(1).split(",").toList
      map(group) = jars
    }
    map
  }

  private val parser: OptionParser[Config] =
    new OptionParser[Config]("renaissance") {
      head("Renaissance Benchmark Suite", "0.1")

      help("help")
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
          "Execution policy, one of: " +
            Policy.descriptions.asScala.keys.mkString(", ")
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
      opt[Unit]("readme")
        .text("Regenerates the README file, and does not run anything.")
        .action((_, c) => c.withReadme(true))
      opt[Unit]("list")
        .text("Print list of benchmarks with their description.")
        .action((_, c) => c.withList())
      opt[Unit]("raw-list")
        .text("Print list of benchmarks, each benchmark name on separate line.")
        .action((_, c) => c.withRawList())
      opt[Unit]("group-list")
        .text("Print list of benchmark groups.")
        .action((_, c) => c.withGroupList())
      arg[String]("benchmark-specification")
        .text("Comma-separated list of benchmarks (or groups) that must be executed.")
        .optional()
        .action((v, c) => c.withBenchmarkSpecification(v))
    }

  private def parse(args: Array[String]): Option[Config] = {
    parser.parse(args, new Config)
  }

  private def camelCase(s: String): String = {
    s.split("-").map(_.capitalize).mkString
  }

  def main(args: Array[String]): Unit = {
    val config = parse(args) match {
      case Some(c) => c
      case None    => sys.exit(1)
    }

    if (config.readme) {
      FileUtils.write(
        new File("README.md"),
        readme,
        java.nio.charset.StandardCharsets.UTF_8,
        false
      )
      FileUtils.write(
        new File("CONTRIBUTION.md"),
        contribution,
        java.nio.charset.StandardCharsets.UTF_8,
        false
      )
      println("README.md and CONTRIBUTION.md updated.")
      return
    } else if (config.printList) {
      print(formatBenchmarkList)
    } else if (config.printRawList) {
      print(formatRawBenchmarkList)
    } else if (config.printGroupList) {
      println(formatGroupList)
    } else if (config.benchmarkSpecifiers.isEmpty) {
      println(parser.usage)
    } else {
      // Check that all the benchmarks on the list really exist.
      val benchmarks = generateBenchmarkList(config)

      // Run the main benchmark loop.
      val failedBenchmarks = new mutable.ArrayBuffer[String](benchmarks.length)
      for (plugin <- config.plugins.asScala) plugin.onCreation()
      try {
        for (benchName <- benchmarks) {
          val bench = loadBenchmark(benchName)
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

  def generateBenchmarkList(config: Config): Seq[String] = {
    val benchmarkSet = new mutable.LinkedHashSet[String]
    for (specifier <- config.benchmarkSpecifiers.asScala) {
      if (benchmarkGroups.contains(specifier)) {
        benchmarkSet += specifier
      } else if (groupBenchmarks.contains(specifier)) {
        benchmarkSet ++= groupBenchmarks(specifier)
      } else {
        println(s"Benchmark (or group) `${specifier}` does not exist.")
        sys.exit(1)
      }
    }

    benchmarkSet.toSeq
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

  private def loadBenchmark(name: String): RenaissanceBenchmark = {
    val mainGroup = benchmarkGroups(name)
    val benchClassName = camelCase(name)
    val packageName = mainGroup.replace("-", ".")
    val fullBenchClassName = "org.renaissance." + packageName + "." + benchClassName

    // Use separate classloader for this benchmark
    val loader = ModuleLoader.getForGroup(mainGroup)

    val benchClass = loader.loadClass(fullBenchClassName)
    val result = benchClass.newInstance()

    // Make current thread as independent of the harness as possible
    Thread.currentThread.setContextClassLoader(loader)

    return result.asInstanceOf[RenaissanceBenchmark]
  }

  private def formatRawBenchmarkList(): String = benchmarks.toSeq.sorted.mkString(", ")

  private def formatBenchmarkList(): String = {
    val indent = "    "

    val result = new StringBuffer
    for (name <- benchmarks.toSeq.sorted) {
      val descriptionWords = benchmarkDetails(name).description.split("\\s+")
      val repetitionsInt = benchmarkDetails(name).defaultRepetitions
      val repetitions = if (repetitionsInt < 0) "not specified" else repetitionsInt.toString
      result.append(name).append("\n")
      result.append(foldText(descriptionWords, 65, indent).mkString("\n"))
      result.append(s"\n${indent}Default repetitions: ${repetitions}\n\n")
    }

    return result.toString
  }

  private def formatGroupList(): String = groupJars.keys.toSeq.sorted.mkString(", ")

  private def generateBenchmarkDescription(name: String): String = {
    val bench = benchmarkDetails(name)
    s"- `${bench.name}` - " +
      s"${bench.description} (default repetitions: ${bench.defaultRepetitions})"
  }

  private def generateBenchmarkList =
    benchmarkGroups
      .groupBy(_._2)
      .toSeq
      .sortBy(_._1)
      .map {
        case (group, benchmarkName) =>
          s"""
##### $group

${benchmarkName
            .map(_._1)
            .toSeq
            .sorted
            .map(generateBenchmarkDescription)
            .mkString("\n\n")}
"""
      }
      .mkString("\n")

  val logoUrl = "https://github.com/D-iii-S/renaissance-benchmarks/" +
    "raw/master/website/resources/images/mona-lisa-round.png"

  lazy val readme = s"""

## Renaissance Benchmark Suite

<p align="center">
  <img height="180px" src="${logoUrl}"/>
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
bundle the JARs and create the final JAR under `target/scala-2.12`.


### Running the benchmarks

To run a Renaissance benchmark, you need to have a JRE installed.
This allows you to execute the following `java` command:

```
java -jar '<renaissance-home>/target/renaissance-0.1.jar' <benchmarks>
```

Above, the `<renaissance-home>` is the path to the root directory of the Renaissance distribution,
and `<benchmarks>` is the list of benchmarks that you wish to run.
For example, you can specify `scala-kmeans` as the benchmark.


#### Complete list of command-line options

The following is a complete list of command-line options.

```
${parser.usage}
```


### List of benchmarks

The following is the complete list of benchmarks, separated into groups.

${generateBenchmarkList}


### Run policies

The suite is designed to support multiple ways of executing a benchmark --
for example, a fixed number of iterations, or a fixed amount of time.
This logic is encapsulated in run policies. Current policies include:

${Policy.descriptions.asScala.map { case (k, v) => s"- `$k` -- $v\n" }.mkString("\n")}


### Plugins and interfacing with external tools

If you are using an external tool to inspect a benchmark, such as an instrumentation agent,
or a profiler, then you will need to make this tool aware of when a benchmark iteration
is starting and when it is ending.
To allow this, the suite allows specifying custom plugins, which are notified when necessary.
Here is an example of how to implement a plugin:

```
class MyPlugin extends ${classOf[Plugin].getSimpleName} {
  def onCreation() = {
    // Initialize the plugin after it has been created.
  }
  def beforeIteration(policy: ${classOf[Policy].getSimpleName}) = {
    // Notify the tool that a benchmark iteration is about to start.
  }
  def afterIteration(policy: ${classOf[Policy].getSimpleName}) = {
    // Notify the tool that the benchmark iteration has ended.
  }
}
```

Here, the ${classOf[Policy].getSimpleName} argument describes
the current state of the benchmark.


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
${benchmarkGroups.keys
    .map { name =>
      val b = benchmarkDetails(name)
      s"| ${b.name} | ${b.licenses.mkString(", ")} | ${b.distro} |"
    }
    .mkString("\n")}


### Design overview

The Renaissance benchmark suite is organized into several `sbt` projects:

- the `renaissance-core` folder that contains a set of *core* classes
  (common interfaces and a harness launcher)
- the `renaissance-harness` folder that contains the actual harness
- the `benchmarks` folder contains a set of *subprojects*, each containing a set of benchmarks
  for a specific domain (and having a separate set of dependencies)

The *core* project is written in pure Java, and it contains the basic benchmark API.
Its most important class is `${classOf[RenaissanceBenchmark].getSimpleName}`,
which must be extended by a concrete benchmark implementation.
This means that each *subproject* depends on the *core* project.

Interfaces of *core* are loaded (when Renaissance is started) by the default
classloader. Every other class (including harness and individual benchmarks)
is loaded by a separate classloader. This separation was done so that there
are never clashes between the different dependencies of the different projects.
Because each benchmark may depend on different versions of external libraries.

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
in the `renaissance-suite.scala` file and in `${classOf[ModuleLoader].getSimpleName}`.


"""

  lazy val contribution = s"""

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
in the `benchmarks` directory, and add a new top-level Scala class
that extends the `${classOf[RenaissanceBenchmark].getSimpleName}` interface.

Here is an example:

```
import org.renaissance._

final class MyJavaBenchmark extends ${classOf[RenaissanceBenchmark].getSimpleName} {
  override def description = "Runs some performance-critical Java code."

  override protected def runIteration(config: ${classOf[Config].getSimpleName}): Unit = {
    // This is the benchmark body, which in this case calls some Java code.
    JavaCode.runSomeJavaCode()
  }
}
```

Above, the name of the benchmark will be automatically generated from the class name.
In this case, the name will be `${RenaissanceBenchmark.kebabCase("MyJavaBenchmark")}`.

To create a new group of benchmarks (for example, benchmarks that depend on a new framework),
create an additional `sbt` project in the `benchmarks` directory,
using an existing project, such as `scala-stdlib`, as an example.
The project will be automatically picked up by the build system
and included into the Renaissance distribution.

Once the benchmark has been added, one needs to make sure to be compliant with the code formatting of the project
(rules defined in `.scalafmt.conf`).
A convenient sbt task can do that check:
```
$$ tools/sbt/bin/sbt renaissanceFormatCheck
```

Another one can directly update the source files to match the desired format:
```
$$ tools/sbt/bin/sbt renaissanceFormat
```

Moreover, the content of the README and CONTRIBUTION files are automatically generated from the codebase.
Updating those files can be done with the `--readme` command-line flag. Using sbt, one would do:
```
$$ tools/sbt/bin/sbt runMain org.renaissance.RenaissanceSuite --readme
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


##### Benchmark criteria

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


##### Release process

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

- Petr Tuma, Charles University in Prague
- Lubomir Bulej, Charles University in Prague
- David Leopoldseder, Johannes Kepler University Linz
- Andrea Rosà, Università della Svizzera italiana
- Gilles Duboscq, Oracle Labs
- Alex Villazon, Universidad Privada Boliviana
- François Farquet, Oracle Labs
- Aleksandar Prokopec, Oracle Labs
"""

}
