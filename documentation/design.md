# Design overview

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
benchmark metadata, such as a summary or a detailed description.
Consequently, each *subproject* depends on the *core* project.
The *core* project also provides APIs that a benchmark needs to work with,
such as the runtime configuration or the policy.

Classes from the *core* are loaded (when Renaissance is started) by the default
classloader. Classes from other projects (including the harness and individual benchmarks)
and external plugins or execution policies are loaded by separate classloaders. This
separation helps ensure that there are no clashes between dependencies of different
projects (each benchmark may depend on different versions of external libraries).

The *harness* project implements the functionality necessary to parse the input
arguments, to run the benchmarks, to generate documentation, and so on. The *harness*
is written in a mix of Java and Scala, and is loaded by the *core* in a separate classloader
to ensure clean environment for running the benchmarks.

The set of subprojects in the `benchmarks` directory are the individual groups of benchmarks
that share a common set of dependencies. A group is typically thematic, relating to
a particular framework or a JVM language, and benchmarks in different groups depend
on a different set of libraries, or even the same libraries with different versions.
The bundling mechanism of the suite takes care that the dependencies of the different groups
never clash with each other.

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
