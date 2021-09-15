# Adding a new benchmark

To add a new benchmark to an existing group, identify the respective project
in the `benchmarks` directory, and add a new top-level Scala (Java) class
that extends (implements) the `Benchmark` interface.

We recommend you also consult [Design overview document](documentation/design.md)
to understand how the whole project is organized.

Here is an example:

```scala
import org.renaissance._
import org.renaissance.Benchmark._

@Summary("Runs some performance-critical Java code.")
final class MyJavaBenchmark extends Benchmark {
  override def run(context: BenchmarkContext): BenchmarkResult = {
    // This is the benchmark body, which in this case calls some Java code.
    JavaCode.runSomeJavaCode()
    // Return object for later validation of the operation result.
    return new MyJavaBenchmarkResult()
  }
}
```

Above, the name of the benchmark will be automatically generated from the class name.
In this case, the name will be `my-java-benchmark`.

To create a new group of benchmarks (for example, benchmarks that depend on a new framework),
create an additional `sbt` project in the `benchmarks` directory,
using an existing project, such as `scala-stdlib`, as an example.
The project will be automatically picked up by the build system
and included into the Renaissance distribution.

Once the benchmark has been added, one needs to make sure to be compliant with the code
formatting of the project (rules defined in `.scalafmt.conf`).
A convenient sbt task can do that check:
```
$ tools/sbt/bin/sbt renaissanceFormatCheck
```

Another one can directly update the source files to match the desired format:
```
$ tools/sbt/bin/sbt renaissanceFormat
```

Moreover, the contents of the `README.md` file is automatically generated
from the codebase. Updating those files can be done with the `--readme` command-line flag.
Using sbt, one would do:

```
$ tools/sbt/bin/sbt runMain org.renaissance.core.Launcher --readme
```
