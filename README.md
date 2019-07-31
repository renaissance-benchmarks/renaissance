

## Renaissance Benchmark Suite

<p align="center">
  <img height="180px" src="https://github.com/renaissance-benchmarks/renaissance/raw/master/website/resources/images/mona-lisa-round.png"/>
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
bundle the JARs and create the final JAR under `target` directory.


### Running the benchmarks

To run a Renaissance benchmark, you need to have a JRE installed.
This allows you to execute the following `java` command:

```
$ java -jar '<renaissance-home>/target/renaissance-gpl-0.10.0.jar' <benchmarks>
```

Above, the `<renaissance-home>` is the path to the root directory of the Renaissance distribution,
and `<benchmarks>` is the list of benchmarks that you wish to run.
For example, you can specify `scala-kmeans` as the benchmark.


#### Complete list of command-line options

The following is a complete list of command-line options.

```
Renaissance Benchmark Suite, version 0.10.0
Usage: renaissance [options] [benchmark-specification]

  -h, --help               Prints this usage text.
  -r, --repetitions <value>
                           Execute the measured operation a fixed number of times.
  -t, --run-seconds <value>
                           Execute the measured operation for a fixed number of seconds.
  --policy <value>         Use policy to control repeated execution of measured operation, specified as <jar-file>!<class-name>.
  --plugin <value>         Load harness plugin, specified as <jar-file>!<class-name>. Can appear multiple times.
  --csv <value>            Output results to CSV file.
  --json <value>           Output results to JSON file.
  --functional-test        Reduce iteration times significantly for testing purposes.
  -c, --configuration <value>
                           Run benchmarks with given named configuration.
  --list                   Print list of benchmarks with their description.
  --raw-list               Print list of benchmarks (each benchmark name on separate line).
  --group-list             Print list of benchmark groups (each group name on separate line).
  benchmark-specification  Comma-separated list of benchmarks (or groups) that must be executed (or all).
```


### List of benchmarks

The following is the complete list of benchmarks, separated into groups.

#### actors

- `akka-uct` - Runs the Unbalanced Cobwebbed Tree actor workload in Akka. (default repetitions: 24)

- `reactors` - Runs benchmarks inspired by the Savina microbenchmark workloads in a sequence on Reactors.IO. (default repetitions: 10)

#### apache-spark

- `als` - Runs the ALS algorithm from the Spark MLlib. (default repetitions: 30)

- `chi-square` - Runs the chi-square test from Spark MLlib. (default repetitions: 60)

- `dec-tree` - Runs the Random Forest algorithm from Spark MLlib. (default repetitions: 40)

- `gauss-mix` - Computes a Gaussian mixture model using expectation-maximization. (default repetitions: 40)

- `log-regression` - Runs the logistic regression workload from the Spark MLlib. (default repetitions: 20)

- `movie-lens` - Recommends movies using the ALS algorithm. (default repetitions: 20)

- `naive-bayes` - Runs the multinomial naive Bayes algorithm from the Spark MLlib. (default repetitions: 30)

- `page-rank` - Runs a number of PageRank iterations, using RDDs. (default repetitions: 20)

#### database

- `db-shootout` - Executes a shootout test using several in-memory databases. (default repetitions: 16)

#### dummy

- `dummy-empty` - A dummy benchmark which only serves to test the harness. (default repetitions: 20)

- `dummy-failing` - A dummy benchmark for testing the harness (fails during iteration). (default repetitions: 20)

- `dummy-setup-failing` - A dummy benchmark for testing the harness (fails during setup). (default repetitions: 20)

- `dummy-teardown-failing` - A dummy benchmark for testing the harness (fails during teardown). (default repetitions: 20)

- `dummy-validation-failing` - A dummy benchmark for testing the harness (fails during validation). (default repetitions: 20)

#### jdk-concurrent

- `fj-kmeans` - Runs the k-means algorithm using the fork/join framework. (default repetitions: 30)

- `future-genetic` - Runs a genetic algorithm using the Jenetics library and futures. (default repetitions: 50)

#### jdk-streams

- `mnemonics` - Solves the phone mnemonics problem using JDK streams. (default repetitions: 16)

- `par-mnemonics` - Solves the phone mnemonics problem using parallel JDK streams. (default repetitions: 16)

- `scrabble` - Solves the Scrabble puzzle using JDK Streams. (default repetitions: 50)

#### neo4j

- `neo4j-analytics` - Executes Neo4J graph queries against a movie database. (default repetitions: 20)

#### rx

- `rx-scrabble` - Solves the Scrabble puzzle using the Rx streams. (default repetitions: 80)

#### scala-dotty

- `dotty` - Runs the Dotty compiler on a set of source code files. (default repetitions: 50)

#### scala-sat

- `scala-doku` - Solves Sudoku Puzzles using Scala collections. (default repetitions: 20)

#### scala-stdlib

- `scala-kmeans` - Runs the K-Means algorithm using Scala collections. (default repetitions: 50)

#### scala-stm

- `philosophers` - Solves a variant of the dining philosophers problem using ScalaSTM. (default repetitions: 30)

- `scala-stm-bench7` - Runs the stmbench7 benchmark using ScalaSTM. (default repetitions: 60)

#### twitter-finagle

- `finagle-chirper` - Simulates a microblogging service using Twitter Finagle. (default repetitions: 90)

- `finagle-http` - Sends many small Finagle HTTP requests to a Finagle HTTP server and awaits response. (default repetitions: 12)




### Execution policies

The suite generally executes the measured operation of a benchmark multiple times
and uses an execution policy to determine how many time to repeat the execution.
By default, the suite supports executing the operation a fixed number of times
and a fixed amount of time. These policies are implicitly selected by setting
the number of iterations or the execution time on the suite command line.

To provide additional control over execution of the measured operation, the
suite also allows to specify a custom execution policy, which has to implement
the ExecutionPolicy interface.


### Plugins and interfacing with external tools

If you are using an external tool to inspect a benchmark, such as an instrumentation agent,
or a profiler, then you will need to make this tool aware of when a benchmark iteration
is starting and when it is ending.
To allow this, the suite allows specifying custom plugins, which are notified when necessary.
Such a plugin needs to implement the `Plugin` marker interface as well as
interfaces from the `Plugin` interface name space which indicate the events
a plugin is interested in.

Here is an example of a simple plugin:

```
class MyPlugin extends Plugin with HarnessInitListener {
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
- `HarnessInitListener`
- `HarnessShutdownListener`
- `BenchmarkSetUpListener`
- `BenchmarkTearDownListener`
- `BenchmarkResultListener`
- `BenchmarkFailureListener`
- `OperationSetUpListener`
- `OperationTearDownListener`

### JMH support

You can also build and run Renaissance with JMH. To build a JMH-enabled JAR, run:

```
$ tools/sbt/bin/sbt renaissanceJmh/jmh:assembly
```

To run the benchmarks using JMH, you can execute the following `java` command:

```
$ java -jar 'renaissance-jmh/target/scala-2.12/renaissance-jmh-assembly-0.10.0.jar'
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
| akka-uct | MIT | MIT |
| als | APACHE2 | MIT |
| chi-square | APACHE2 | MIT |
| db-shootout | APACHE2 | MIT |
| dec-tree | APACHE2 | MIT |
| dotty | BSD3 | MIT |
| dummy-empty | MIT | MIT |
| dummy-failing | MIT | MIT |
| dummy-setup-failing | MIT | MIT |
| dummy-teardown-failing | MIT | MIT |
| dummy-validation-failing | MIT | MIT |
| finagle-chirper | APACHE2 | MIT |
| finagle-http | APACHE2 | MIT |
| fj-kmeans | APACHE2 | MIT |
| future-genetic | APACHE2 | MIT |
| gauss-mix | APACHE2 | MIT |
| log-regression | APACHE2 | MIT |
| mnemonics | MIT | MIT |
| movie-lens | APACHE2 | MIT |
| naive-bayes | APACHE2 | MIT |
| neo4j-analytics | GPL3 | GPL3 |
| page-rank | APACHE2 | MIT |
| par-mnemonics | MIT | MIT |
| philosophers | BSD3 | MIT |
| reactors | MIT | MIT |
| rx-scrabble | GPL2 | GPL3 |
| scala-doku | MIT | MIT |
| scala-kmeans | MIT | MIT |
| scala-stm-bench7 | BSD3, GPL2 | GPL3 |
| scrabble | GPL2 | GPL3 |


### Design overview

The Renaissance benchmark suite is organized into several `sbt` projects:

- the `renaissance-core` folder that contains a set of *core* classes
  (common interfaces and a harness launcher)
- the `renaissance-harness` folder that contains the actual harness
- the `benchmarks` folder contains a set of *subprojects*, each containing a set of benchmarks
  for a specific domain (and having a separate set of dependencies)

The *core* project is written in pure Java, and it contains the basic benchmark API.
Its most important elements are the `Benchmark` interface,
which must be implemented by each benchmark, and the annotations in the
`Benchmark` interface name space, which are used to provide
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
in the `renaissance-suite.scala` file and in `ModuleLoader`.


