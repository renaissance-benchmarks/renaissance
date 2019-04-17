package org.renaissance

import java.io.File
import java.net.URLClassLoader
import java.nio.charset.StandardCharsets
import org.apache.commons.io.FileUtils
import org.apache.commons.io.IOUtils
import scala.collection._
import scala.collection.JavaConverters._
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
        .action((v, c) => c.withRepetitions(v))
      opt[String]("policy")
        .text("Execution policy, one of: " +
          Policy.descriptions.asScala.keys.mkString(", "))
        .action((v, c) => c.withPolicy(v))
      opt[String]("plugins")
        .text("Comma-separated list of class names of plugin implementations.")
        .action((v, c) => c.withPlugins(v))
      opt[Unit]("readme")
        .text("Regenerates the README file, and does not run anything.")
        .action((_, c) => c.withReadme(true))
      opt[Unit]("list")
        .text("Print list of benchmarks with their description.")
        .action((_, c) => c.withList())
      opt[Unit]("raw-list")
        .text("Print list of benchmarks, each benchmark name on separate line.")
        .action((_, c) => c.withRawList())
      arg[String]("benchmark-specification")
        .text("Comma-separated list of benchmarks (or groups) that must be executed.")
        .optional()
        .action((v, c) => c.withBenchmarkSpecification(v))
    }

  private def parse(args: Array[String]): Option[Config] = {
    parser.parse(args, new Config)
  }

  private def copyJars(mainGroup: String): Unit = {
    // Copy all the JAR files for this group of benchmarks.
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
    } else if (config.printList) {
      print(formatBenchmarkList)
    } else if (config.printRawList) {
      print(formatRawBenchmarkList)
    } else {
      // Check that all the benchmarks on the list really exist.
      for (benchName <- config.benchmarkList.asScala) {
        if (!(benchmarkGroups.contains(benchName))) {
          println(s"Benchmark `${benchName}` does not exist.")
          sys.exit(1)
        }
      }

      // Run the main benchmark loop.
      for (plugin <- config.plugins.asScala) plugin.onCreation()
      try {
        for (benchName <- config.benchmarkList.asScala) {
          val bench = loadBenchmark(benchName)
          val exception = bench.runBenchmark(config)
          if (exception.isPresent) {
            Console.err.println(s"Exception occurred in ${bench}: ${exception.get.getMessage}")
            exception.get.printStackTrace()
          }
        }
      } finally {
        for (plugin <- config.plugins.asScala) plugin.onExit()
      }
    }
  }

  def foldText(words: Seq[String], width: Int, indent: String): Seq[String] = {
    var column = 0
    val line = new StringBuffer
    val result = new scala.collection.mutable.ArrayBuffer[String]
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

  private def loadBenchmark(name: String): ProxyRenaissanceBenchmark = {
    val mainGroup = benchmarkGroups(name)
    copyJars(mainGroup)

    val dir = "target/modules/" + mainGroup + "/"
    val urls = for {
      file <- new File(dir).listFiles()
      if file.getName.endsWith(".jar")
    } yield file.toURI.toURL
    val loader = new URLClassLoader(urls, ClassLoader.getSystemClassLoader.getParent)
    val benchClassName = camelCase(name)
    val packageName = mainGroup.replace("-", ".")
    val fullBenchClassName = "org.renaissance." + packageName + "." + benchClassName
    new ProxyRenaissanceBenchmark(loader, fullBenchClassName)
  }

  private def formatRawBenchmarkList(): String = {
    val result = new StringBuffer
    for (name <- benchmarks.toSeq.sorted) {
      result.append(name + "\n")
    }

    return result.toString
  }

  private def formatBenchmarkList(): String = {
    val indent = "    "
    val details = new java.util.Properties
    details.load(getClass.getResourceAsStream("/benchmark-details.properties"))

    val result = new StringBuffer
    for (name <- benchmarks.toSeq.sorted) {
      val description = details.getProperty(
        "benchmark." + name + ".description",
        "Description not provided"
      )
      val descriptionWords = description.split("\\s+")
      val repetitions = details.getProperty(
        "benchmark." + name + ".repetitions",
        "Not specified"
      )
      result.append(name + "\n")
      result.append(foldText(descriptionWords, 65, indent).mkString("\n"))
      result.append(s"\n${indent}Default repetitions: ${repetitions}\n\n")
    }

    return result.toString
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

  val logoUrl = "https://github.com/D-iii-S/renaissance-benchmarks/" +
    "raw/master/website/resources/images/mona-lisa-round.png"

  lazy val readme = s"""

# Renaissance Benchmark Suite

<p align="center">
  <img height="180px" src="${logoUrl}"/>
</p>


The Renaissance Benchmark Suite aggregates common modern JVM workloads,
including, but not limited to, Big Data, machine-learning, and functional programming.
The suite is intended to be used to optimize just-in-time compilers, interpreters, GCs,
and for tools such as profilers, debuggers, or static analyzers, and even different hardware.
It is intended to be an open-source, collaborative project,
in which the community can propose and improve benchmark workloads.

The contents of this README file are automatically generated from the codebase,
and can be refreshed with the `--readme` command-line flag.


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
java -jar '<renaissance-home>/target/scala-2.12/renaissance-0.1.jar' <benchmarks>
```

Above, the `<renaissance-home>` is the path to the root directory of the Renaissance distribution,
and `<benchmarks>` is the list of benchmarks that you wish to run.
For example, you can specify `scala-k-means` as the benchmark.


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

Please see CONTRIBUTION.md for a description of the contributing process.


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
      val b = loadBenchmark(name)
      s"| ${b.name()} | ${b.licenses().mkString(", ")} | ${b.distro()} |"
    }
    .mkString("\n")}


### Design overview

The Renaissance benchmark suite is organized into several `sbt` projects:

- the `renaissance-core` folder that contains a set of *core* classes
- the `benchmarks` folder contains a set of *subprojects*, each containing a set of benchmarks
  for a specific domain (and having a separate set of dependencies)
- the top-level `src` folder contains the *harness*

The *subprojects* that correspond to different groups of benchmarks
generally depend on different versions of external libraries.
If they depend on Scala, then their Scala version can be different
from the Scala version that the Renaissance harness is written in.
The separation into subprojects was done so that there are never clashes
between the different dependencies of the different projects.

The *core* project is written in pure Java, and it contains the basic benchmark API.
Its most important class is `${classOf[RenaissanceBenchmark].getSimpleName}`,
which must be extended by a concrete benchmark implementation.
This means that each *subproject* depends on the *core* project.

The *harness* project implements the functionality that is necessary
to parse the input arguments, to run the benchmarks, to generate documentation, and so on.
It depends on the *core* project, but it does not depend on the *subprojects* directly.
Instead, the JARs of the subprojects are copied as the generated *resources*
of the *harness* project, and embedded into the resulting JAR artifact.

```
renaissance-core
  ^           ^
  |            \\  (classpath dep.)
  |             \\
  |              ---- subproject X
  |                      .
  |                      .
  | (classpath dep.)     .
  |                      .
renaissance harness  <.... (JARs copied as resources)
```

When the harness is started, it uses the input arguments to select the benchmark,
and then unpacks the JARs of the corresponding benchmark group into a scratch folder.
The harness then creates a classloader with the unpacked JARs and loads the benchmark group.
The class loader is created directly below the bootstrap class loader.
This ensures that the classpath dependencies in the system class loader (of the harness)
are never mixed with any dependencies of a benchmark (which is in the URL class loader).

```
         boot class loader (JDK)
          ^              ^
          |              |
system class loader    URL class loader
    (harness)             (benchmark)
```

We need to do this to, e.g., avoid accidentally resolving the wrong class
by going through the system class loader (this can easily happen with,
e.g. Apache Spark and Scala, due to the way that Spark internally resolves some classes).
Note that, as a result, the `renaissance-core` JAR is loaded twice -- once in the harness,
and separately in the URL class loader of the specified benchmark.
To enable the harness to call the methods of the
`${classOf[RenaissanceBenchmark].getSimpleName}` that is loaded in the URL class loader,
we have a special `${classOf[ProxyRenaissanceBenchmark].getSimpleName}` class,
that knows how to call the methods of the benchmark defined in another class loader.

You can see the further details of the build system in the top-level `build.sbt` file,
and in the `renaissance-suite.scala` file.


"""

  lazy val contribution = s"""

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

Above, the name of the benchmark will be automatically generated from the class name.
In this case, the name will be `${RenaissanceBenchmark.kebabCase("MyJavaBenchmark")}`.

To create a new group of benchmarks (for example, benchmarks that depend on a new framework),
create an additional `sbt` project in the `benchmarks` directory,
using an existing project, such as `scala-stdlib`, as an example.
The project will be automatically picked up by the build system
and included into the Renaissance distribution.


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
- François Farquet, Oracle Labs
- Aleksandar Prokopec, Oracle Labs
"""

}
