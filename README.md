

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
java -jar '<renaissance-home>/target/renaissance-0.9.0.jar' <benchmarks>
```

Above, the `<renaissance-home>` is the path to the root directory of the Renaissance distribution,
and `<benchmarks>` is the list of benchmarks that you wish to run.
For example, you can specify `scala-kmeans` as the benchmark.


#### Complete list of command-line options

The following is a complete list of command-line options.

```
Renaissance Benchmark Suite, version 0.9.0
Usage: renaissance [options] [benchmark-specification]

  --help                   Prints this usage text.
  -r, --repetitions <value>
                           Number of repetitions used with the fixed-iterations policy.
  -w, --warmup-seconds <value>
                           Number of warmup seconds, when using time-based policies.
  -t, --run-seconds <value>
                           Number of seconds to run after the warmup, when using time-based policies.
  --policy <value>         Execution policy, one of: fixed-warmup, fixed-iterations
  --plugins <value>        Comma-separated list of class names of plugin implementations.
  --csv <value>            Output results to CSV file.
  --json <value>           Output results to JSON file.
  --readme                 Regenerates the README file, and does not run anything.
  --functional-test        Reduce iteration times significantly for testing purposes.
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

- `als` - Runs the ALS algorithm from the Spark MLlib. (default repetitions: 60)

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

- `dummy` - A dummy benchmark which only serves to test the harness. (default repetitions: 20)

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

#### scala-stdlib

- `scala-kmeans` - Runs the K-Means algorithm using Scala collections. (default repetitions: 50)

#### scala-stm

- `philosophers` - Solves a variant of the dining philosophers problem using ScalaSTM. (default repetitions: 30)

- `scala-stm-bench7` - Runs the stmbench7 benchmark using ScalaSTM. (default repetitions: 60)

#### twitter-finagle

- `finagle-chirper` - Simulates a microblogging service using Twitter Finagle. (default repetitions: 90)

- `finagle-http` - Sends many small Finagle HTTP requests to a Finagle HTTP server and awaits response. (default repetitions: 12)




### Run policies

The suite is designed to support multiple ways of executing a benchmark --
for example, a fixed number of iterations, or a fixed amount of time.
This logic is encapsulated in run policies. Current policies include:

- `fixed-warmup` -- Warms up the VM by running the benchmark a fixed amount of time, and then runs the benchmark again for some fixed amount of time (use `-w` and `-t`).

- `fixed-iterations` -- Runs the benchmark for a fixed number of iterations (use `-r`).



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
| akka-uct | MIT | MIT |
| als | APACHE2 | MIT |
| chi-square | APACHE2 | MIT |
| db-shootout | APACHE2 | MIT |
| dec-tree | APACHE2 | MIT |
| dotty | BSD3 | MIT |
| dummy | MIT | MIT |
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
Its most important class is `RenaissanceBenchmark`,
which must be extended by a concrete benchmark implementation, and the
annotations in the `Benchmark` class, which are
used to set static information about a benchmark, such as a summary or
detailed description.
Consequently, each *subproject* depends on the *core* project.

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
in the `renaissance-suite.scala` file and in `ModuleLoader`.


