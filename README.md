
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
need to run `sbt` build tool as follows:

```
$ tools/sbt/bin/sbt assembly
```

This will retrieve all the dependencies, compile all the benchmark projects and the harness,
bundle the JARs and create the final JAR under the `target` directory.


### Running the benchmarks

To run a Renaissance benchmark, you need to have a JRE installed.
This allows you to execute the following `java` command:

```
$ java -jar '<renaissance-home>/target/renaissance-gpl-0.11.0.jar' <benchmarks>
```

Above, the `<renaissance-home>` is the path to the root directory of the Renaissance distribution,
and `<benchmarks>` is the list of benchmarks that you wish to run.
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
Renaissance Benchmark Suite, version 0.11.0
Usage: renaissance [options] [benchmark-specification]

  -h, --help               Prints this usage text.
  -r, --repetitions <count>
                           Execute the measured operation a fixed number of times.
  -t, --run-seconds <seconds>
                           Execute the measured operation for fixed time (wall-clock).
  --operation-run-seconds <seconds>
                           Execute the measured operation for fixed accumulated operation time (wall-clock).
  --policy <class-path>!<class-name>
                           Use policy plugin to control repetition of measured operation execution.
  --plugin <class-path>!<class-name>
                           Load external plugin. Can appear multiple times.
  --with-arg <value>       Adds an argument to the plugin or policy specified last. Can appear multiple times.
  --csv <csv-file>         Output results as CSV to <csv-file>.
  --json <json-file>       Output results as JSON to <json-file>.
  -c, --configuration <conf-name>
                           Use benchmark parameters from configuration <conf-name>.
  --scratch-base <dir>     Create scratch directories in <dir>. Defaults to current directory.
  --keep-scratch           Keep the scratch directories after VM exit. Defaults to deleting scratch directories.
  --no-forced-gc           Do not force garbage collection before each measured operation. Defaults to forced GC.
  --no-jvm-check           Do not check benchmark JVM version requirements (for execution or raw-list).
  --list                   Print the names and descriptions of all benchmarks.
  --raw-list               Print the names of benchmarks compatible with this JVM (one per line).
  --group-list             Print the names of all benchmark groups (one per line).
  benchmark-specification  List of benchmarks (or groups) to execute (or 'all').

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

- `dummy-param` - A dummy benchmark for testing the harness (test configurable parameters). (default repetitions: 20)

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
harness state and benchmark execution. A plugin is a user-defined class which must implement
the `Plugin` marker interface and provide at least a default (parameter-less)
constructor. However, such a minimal plugin would not receive any notifications. To receive
notifications, the plugin class must implement interfaces from the `Plugin`
interface name space depending on the type of events it wants to receive, or services it wants
to provide. This is demonstrated in the following example:

```scala
class SimplePlugin extends Plugin
  with AfterHarnessInitListener
  with AfterOperationSetUpListener
  with BeforeOperationTearDownListener {

  override def afterHarnessInit() = {
    // Initialize the plugin after the harness finished initializing
  }

  override def afterOperationSetUp(benchmark: String, index: Int) = {
    // Notify the tool that the measured operation is about to start.
  }

  override def beforeOperationTearDown(benchmark: String, index: Int) = {
    // Notify the tool that the measured operations has finished.
  }
}
```

The following interfaces provide common (paired) event types which allow a plugin to hook
into a specific point in the benchmark execution sequence. They are analogous to common
annotations known from testing frameworks such as JUnit. Harness-level events occur only
once per the whole execution, benchmark-level events occur once for each benchmark
executed, and operation-level events occur once for each execution of the measured
operation.
- `AfterHarnessInitListener`, `BeforeHarnessShutdownListener`
- `BeforeBenchmarkSetUpListener`, `AfterBenchmarkTearDownListener`
- `AfterBenchmarkSetUpListener`, `BeforeBenchmarkTearDownListener`
- `AfterOperationSetUpListener`, `BeforeOperationTearDownListener`

The following interfaces provide special non-paired event types:
- `MeasurementResultListener`, intended for plugins that want to receive
measurements results (perhaps to store them in a custom format). The harness calls the
`onMeasurementResult` method with the name of the metric and its value, but only if the
benchmark operation produces a valid result.
- `BenchmarkFailureListener`, which indicates that the benchmark execution
has either failed in some way (the benchmark triggered an exception), or that the benchmark
operation produced a result which failed validation. This means that no measurements results
will be received.

And finally the following interfaces are used by the harness to request
services from plugins:
- `MeasurementResultPublisher`, intended for plugins that want to collect
values of additional metrics around the execution of the benchmark operation. The harness
calls the `onMeasurementResultsRequested` method with an instance of event dispatcher which
the plugin is supposed to use to notify other result listeners about custom measurement results.
- `ExecutionPolicy`, intended for plugins that want to control the execution
of the benchmark's measured operation. Such a plugin should implement other interfaces to
get enough information to determine, per-benchmark, whether to execute the measured operation
or not. The harness calls the `canExecute` method before executing the benchmark's measured
operation, and will pass the result of the `isLast` method to some other events.

To make the harness use an external plugin, it needs to be specified on the command line.
The harness can load multiple plugins, and each must be enabled using the
`--plugin <class-path>!<class-name>` option. The `<class-path>` is the class path on which
to look for the plugin class, and `<class-name>` is a fully qualified name of the plugin class.
Custom execution policy must be enabled using the `--policy <class-path>!<class-name>` option.
The syntax is the same as in case of normal plugins (and the policy is also a plugin, which
can register for all event types), but this option tells the harness to actually use the
plugin to control benchmark execution. Other than that, policy is treated the same was as
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
arguments to that plugin (or policy). A plugin that wants to receive command line arguments
must define a constructor which takes an array of strings (`String[]`) or a string vararg
(`String...`) as parameter. The harness tries to use this constructor first and falls back
to the default (parameter-less) constructor.


### JMH support

You can also build and run Renaissance with JMH. To build a JMH-enabled JAR, run:

```
$ tools/sbt/bin/sbt renaissanceJmh/jmh:assembly
```

To run the benchmarks using JMH, you can execute the following `java` command:

```
$ java -jar 'renaissance-jmh/target/scala-2.12/renaissance-jmh-assembly-0.11.0.jar'
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
The following table contains the licensing information (and JVM version
requirements) for all the benchmarks:

| Benchmark        | Licenses   | Distro | JVM required (min) | JVM supported (max) |
| :--------------- | :--------- | :----: | :----------------: | :-----------------: |
| akka-uct | MIT | MIT | 1.8 |  |
| als | APACHE2 | MIT | 1.8 |  |
| chi-square | APACHE2 | MIT | 1.8 |  |
| db-shootout | APACHE2 | MIT | 1.8 |  |
| dec-tree | APACHE2 | MIT | 1.8 |  |
| dotty | BSD3 | MIT | 1.8 |  |
| finagle-chirper | APACHE2 | MIT | 1.8 |  |
| finagle-http | APACHE2 | MIT | 1.8 |  |
| fj-kmeans | APACHE2 | MIT | 1.8 |  |
| future-genetic | APACHE2 | MIT | 1.8 |  |
| gauss-mix | APACHE2 | MIT | 1.8 |  |
| log-regression | APACHE2 | MIT | 1.8 |  |
| mnemonics | MIT | MIT | 1.8 |  |
| movie-lens | APACHE2 | MIT | 1.8 |  |
| naive-bayes | APACHE2 | MIT | 1.8 |  |
| neo4j-analytics | GPL3 | GPL3 | 11 | 15 |
| page-rank | APACHE2 | MIT | 1.8 |  |
| par-mnemonics | MIT | MIT | 1.8 |  |
| philosophers | BSD3 | MIT | 1.8 |  |
| reactors | MIT | MIT | 1.8 |  |
| rx-scrabble | GPL2 | GPL3 | 1.8 |  |
| scala-doku | MIT | MIT | 1.8 |  |
| scala-kmeans | MIT | MIT | 1.8 |  |
| scala-stm-bench7 | BSD3, GPL2 | GPL3 | 1.8 |  |
| scrabble | GPL2 | GPL3 | 1.8 |  |


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
and external plugins or execution policies are loaded by separate classloaders. This
separation helps ensure that there are no clashes between dependencies of different
projects (each benchmark may depend on different versions of external libraries).

The *harness* project implements the functionality necessary to parse the input
arguments, to run the benchmarks, to generate documentation, and so on. The *harness*
is written in a mix of Java and Scala, and is loaded by the *core* in a separate classloader
to ensure clean environment for running the benchmarks.

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
and then unpacks the JARs of the corresponding benchmark group into a temporary directory.
The harness then creates a classloader that searches the unpacked JARs and loads the
benchmark group. The class loader is created directly below the default class loader.
Because the default class loader contains only base JRE classes and common interfaces
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

You can find further details in the top-level `build.sbt` file, and in the source code of
the `RenaissanceSuite` and `ModuleLoader` classes.
