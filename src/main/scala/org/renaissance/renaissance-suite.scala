package org.renaissance

import java.io.File
import java.net.URLClassLoader
import java.nio.charset.StandardCharsets
import org.apache.commons.io.FileUtils
import org.apache.commons.io.IOUtils
import scala.collection._
import scopt._

object RenaissanceSuite {

  val benchmarkGroups = {
    val map = new mutable.HashMap[String, String]
    val lines = IOUtils.lineIterator(
      getClass.getResourceAsStream("/benchmark-group.txt"),
      StandardCharsets.UTF_8)
    while (lines.hasNext) {
      val line = lines.next()
      val parts = line.split("=")
      map(parts(0)) = parts(1)
    }
    map
  }

  val benchmarks = benchmarkGroups.keys

  val groupJars = {
    val map = new mutable.HashMap[String, List[String]]
    val lines = IOUtils.lineIterator(
      getClass.getResourceAsStream("/groups-jars.txt"),
      StandardCharsets.UTF_8)
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
        .text("Number of repetitions of each benchmark")
        .action((v, c) => c.copy(repetitions = v))
      opt[String]("policy")
        .text("Execution policy, one of: " + Policy.descriptions.keys.mkString(", "))
        .action((v, c) => c.copy(policy = v))
      opt[String]("plugins")
        .text("Comma-separated list of class names of plugin implementations.")
        .action((v, c) => c.withPlugins(v))
      opt[Unit]("readme")
        .text("Regenerates the README file, and does not run anything.")
        .action((_, c) => c.copy(readme = true))
      arg[String]("benchmark-specification")
        .text("Comma-separated list of benchmarks (or groups) that must be executed.")
        .optional()
        .action((v, c) => c.withBenchmarkSpecification(v))
    }

  private def parse(args: Array[String]): Option[Config] = {
    parser.parse(args, new Config)
  }

  private def copyJars(mainGroup: String): Unit = {
    val jars = groupJars(mainGroup)
    for (jar <- jars) {
      val is = getClass.getResourceAsStream("/" + jar)
      FileUtils.copyToFile(is, new File("target/modules/" + mainGroup, jar.split("/").last))
    }
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
        false)
      FileUtils.write(
        new File("CONTRIBUTION.md"),
        contribution,
        java.nio.charset.StandardCharsets.UTF_8,
        false)
      println("README.md and CONTRIBUTION.md updated.")
      return
    } else {
      // Check that all the benchmarks on the list really exist.
      for (benchName <- config.benchmarkList) {
        if (!(benchmarkGroups.contains(benchName))) {
          println(s"Benchmark `${benchName}` does not exist.")
          sys.exit(1)
        }
      }

      // Run the main benchmark loop.
      for (plugin <- config.plugins) plugin.onCreation()
      try {
        for (benchName <- config.benchmarkList) {
          val bench = loadBenchmark(benchName)
          bench.runBenchmark(config)
        }
      } finally {
        for (plugin <- config.plugins) plugin.onExit()
      }
    }
  }

  private def loadBenchmark(name: String): RenaissanceBenchmark = {
    val mainGroup = benchmarkGroups(name)
    copyJars(mainGroup)

    val dir = "target/modules/" + mainGroup + "/"
    val urls = for {
      file <- new File(dir).listFiles()
      if file.getName.endsWith(".jar")
    } yield file.toURI.toURL
    val loader = new URLClassLoader(urls, this.getClass.getClassLoader)
    val benchClassName = camelCase(name)
    val packageName = mainGroup.replace("-", ".")
    val benchClass =
      loader.loadClass("org.renaissance." + packageName + "." + benchClassName)
    benchClass.newInstance.asInstanceOf[RenaissanceBenchmark]
  }

  private def generateBenchmarkDescription(name: String): String = {
    val bench = loadBenchmark(name)
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

  val readme = s"""

# Renaissance Benchmark Suite

The Renaissance Benchmark Suite aggregates common modern JVM workloads,
including, but not limited to, Big Data, machine-learning, and functional programming.
The suite is intended to be used to optimize just-in-time compilers, interpreters, GCs,
and for tools such as profilers, debuggers, or static analyzers, and even different hardware.
It is intended to be an open-source, collaborative project,
in which the community can propose and improve benchmark workloads.

The contents of this README file are automatically generated from the codebase,
and can be refreshed with the `--readme` command-line flag.


### Building the suite

To build the suite and bundle it, you need to first start the included `sbt` build tool:

```
$$ tools/sbt/bin/sbt
```

This will open the `sbt` shell, from which you can issue various build commands.
To bundle the suite, run:

```
> renaissanceBundle
```

This will retrieve all the dependencies, compile all the benchmark projects and the harness,
bundle the JARs of the subprojects into the JAR of the suite, copy all the dependencies
to the `target/renaissance` directory, and produce a `tar` file in the `target` directory.


### Running the benchmarks

To run a Renaissance benchmark, you need to have a JRE installed.
This allows you to execute the following `java` command:

```
java -cp '<renaissance-home>/jars/*' org.renaissance.RenaissanceSuite <benchmarks>
```

Above, the `<renaissance-home>` is the path to the root directory of the Renaissance distribution,
and `<benchmarks>` is the list of benchmarks that you wish to run.
For example, you can specify `k-means-scala` as the benchmark.


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

${Policy.descriptions.map { case (k, v) => s"- `$k` -- $v\n" }.mkString("\n")}


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

Please see CONTRIBUTION.md for a description of the contributing process.
"""

  val contribution = s"""

## Contribution Guide

### Code organization and internals

The code is organized into three main parts:

- `renaissance-core`: these are the core APIs that a benchmark needs to work with,
  such as the runtime configuration, the benchmark base class or the policy.
- `renaissance`: this is the overall suite project, which is responsible for running the harness,
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

To create a new group of benchmarks (for example, benchmarks that depend on a new framework),
create an additional `sbt` project in the `benchmarks` directory,
using an existing project, such as `scala-stdlib`, as an example.
The project will be automatically picked up by the build system
and included into the Renaissance distribution.


### Benchmark evaluation and release process

In the open-source spirit, anyone can propose an additional benchmark by creating pull request.
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
to profilerate the most important ones, and publish them as *major releases*.
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
- Francois Farquet, Oracle Labs
- Aleksandar Prokopec, Oracle Labs
"""

}
