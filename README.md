

## Renaissance Benchmark Suite

<p align="center">
  <img height="180px" src="https://github.com/D-iii-S/renaissance-benchmarks/raw/master/website/resources/images/mona-lisa-round.png"/>
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
$ tools/sbt/bin/sbt assembly
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
For example, you can specify `scala-kmeans` as the benchmark.


#### Complete list of command-line options

The following is a complete list of command-line options.

```
Renaissance Benchmark Suite 0.1
Usage: renaissance [options] [benchmark-specification]

  --help                   Prints this usage text.
  -r, --repetitions <value>
                           Number of repetitions of each benchmark
  --policy <value>         Execution policy, one of: fixed
  --plugins <value>        Comma-separated list of class names of plugin implementations.
  --readme                 Regenerates the README file, and does not run anything.
  --list                   Print list of benchmarks with their description.
  --raw-list               Print list of benchmarks, each benchmark name on separate line.
  benchmark-specification  Comma-separated list of benchmarks (or groups) that must be executed.
```


### List of benchmarks

The following is the complete list of benchmarks, separated into groups.


##### actors

- `akka-uct` - Runs the Unbalanced Cobwebbed Tree actor workload in Akka. (default repetitions: 24)


##### apache-spark

- `als` - Runs the ALS algorithm from the Spark MLlib. (default repetitions: 60)

- `chi-square` - Runs the chi-square test from Spark MLlib. (default repetitions: 60)

- `dec-tree` - Runs the Random Forest algorithm from Spark MLlib. (default repetitions: 40)

- `gauss-mix` - Computes a Gaussian mixture model using expectation-maximization. (default repetitions: 40)

- `log-regression` - Runs the logistic regression workload from the Spark MLlib. (default repetitions: 20)

- `movie-lens` - Recommends movies using the ALS algorithm. (default repetitions: 20)

- `naive-bayes` - Runs the multinomial naive Bayes algorithm from the Spark MLlib. (default repetitions: 30)

- `page-rank` - Runs a number of PageRank iterations, using RDDs. (default repetitions: 20)


##### core

- `dummy` - A dummy benchmark, which does no work. It is used only to test the harness. (default repetitions: 20)


##### database

- `db-shootout` - Executes a shootout test using several in-memory databases. (default repetitions: 16)


##### jdk-concurrent

- `future-genetic` - Runs a genetic algorithm using the Jenetics library and futures. (default repetitions: 50)


##### jdk-streams

- `mnemonics` - Solves the phone mnemonics problem using JDK streams. (default repetitions: 16)

- `par-mnemonics` - Solves the phone mnemonics problem using parallel JDK streams. (default repetitions: 16)

- `scrabble` - Solves the Scrabble puzzle using JDK Streams. (default repetitions: 50)


##### neo4j

- `neo4j-analytics` - Executes Neo4J graph queries against a movie database. (default repetitions: 20)


##### rx

- `rx-scrabble` - Solves the Scrabble puzzle using the Rx streams. (default repetitions: 80)


##### scala-dotty

- `dotty` - Runs the Dotty compiler on a set of source code files. (default repetitions: 50)


##### scala-stdlib

- `scala-kmeans` - Runs the K-Means algorithm using Scala collections. (default repetitions: 50)


##### scala-stm

- `philosophers` - Solves a variant of the dining philosophers problem using ScalaSTM. (default repetitions: 30)

- `scala-stm-bench7` - Runs the stmbench7 benchmark using ScalaSTM. (default repetitions: 60)


##### twitter-finagle

- `finagle-chirper` - Simulates a microblogging service using Twitter Finagle. (default repetitions: 90)

- `finagle-http` - Sends many small Finagle HTTP requests to a Finagle HTTP server, and awaits the response. (default repetitions: 12)



### Run policies

The suite is designed to support multiple ways of executing a benchmark --
for example, a fixed number of iterations, or a fixed amount of time.
This logic is encapsulated in run policies. Current policies include:

- `fixed` -- Runs the benchmark for a fixed number of iterations.



### Plugins and interfacing with external tools

If you are using an external tool to inspect a benchmark, such as an instrumentation agent,
or a profiler, then you will need to make this tool aware of when a benchmark iteration
is starting and when it is ending.
To allow this, the suite allows specifying custom plugins, which are notified when necessary.
Here is an example of how to implement a plugin:

```
class MyPlugin extends Plugin {
  def onCreation() = {
    // Initialize the plugin after it has been created.
  }
  def beforeIteration(policy: Policy) = {
    // Notify the tool that a benchmark iteration is about to start.
  }
  def afterIteration(policy: Policy) = {
    // Notify the tool that the benchmark iteration has ended.
  }
}
```

Here, the Policy argument describes
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
| gauss-mix | APACHE2 | MIT |
| finagle-chirper | APACHE2 | MIT |
| philosophers | BSD3 | MIT |
| rx-scrabble | GPL2 | GPL3 |
| dec-tree | APACHE2 | MIT |
| naive-bayes | APACHE2 | MIT |
| db-shootout | APACHE2 | MIT |
| page-rank | APACHE2 | MIT |
| scrabble | GPL2 | GPL3 |
| dummy | MIT | MIT |
| future-genetic | APACHE2 | MIT |
| scala-stm-bench7 | BSD3, GPL2 | GPL3 |
| chi-square | APACHE2 | MIT |
| log-regression | APACHE2 | MIT |
| movie-lens | APACHE2 | MIT |
| scala-kmeans | MIT | MIT |
| akka-uct | MIT | MIT |
| mnemonics | MIT | MIT |
| als | APACHE2 | MIT |
| par-mnemonics | MIT | MIT |
| neo4j-analytics | GPL3 | GPL3 |
| finagle-http | APACHE2 | MIT |
| dotty | BSD3 | MIT |


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
Its most important class is `RenaissanceBenchmark`,
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
  |            \  (classpath dep.)
  |             \
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
`RenaissanceBenchmark` that is loaded in the URL class loader,
we have a special `ProxyRenaissanceBenchmark` class,
that knows how to call the methods of the benchmark defined in another class loader.

You can see the further details of the build system in the top-level `build.sbt` file,
and in the `renaissance-suite.scala` file.


