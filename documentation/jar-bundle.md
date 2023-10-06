# Renaissance JAR bundle contents

This document describes the internal structure of the fat JAR bundle with the
benchmark, which can be either downloaded, or found in the `target` directory
after the `renaissancePackage` SBT command completes successfully.

The bundle is internally laid out as follows:

```
/ (bundle root)
|
+-- META-INF/MANIFEST.MF
|
+-- org/**/*.class (renaissance-core classes)
|
+-- shared/*.jar (shared dependency JAR files)
|
+-- single/*.jar (benchmark JAR files for standalone execution)
|
+-- unique/*/*.jar (dependency JAR files unique to modules)
|
+-- benchmarks.properties
|
`-- modules.properties
```

The `META-INF` directory holds the JAR manifest (`MANIFEST.MF`) which contains
(in addition to standard information) details such Renaissance version and the 
Git commit the bundle was built from.

The `org` directory is just the first of the package directories containing
the `renaissance-core` classes. This ensures that the core classes are always
available when constructing a class loader with a default parent. In addition,
these classes also contain the launcher class, which is used to run the
benchmarks directly from the bundle, which is the typical usage.

Everything else, including the benchmark harness, is loaded as a separate
module with its own dependencies. The dependency JAR files for each module can
be found in two directories. The `shared` directory contains JAR files that
are common to at least two modules to avoid duplicating JAR files in the
bundle. The `unique` directory contains a subdirectory for each module, which
contains jar files that are unique to that module. The list of JAR files for
each module is stored in the `modules.properties` file.

The `benchmarks.properties` file contains metadata about all benchmarks in
the bundle. Property keys specific to a particular benchmark start with the
`benchmark.<benchmark-name>` prefix, and capture the following information:

 * benchmark name and description
 * benchmark module and main class
 * supported JVM versions (min, max)
 * default number of repetitions
 * configurable parameters with default values
 * named configurations (parameter overrides, e.g., for smaller workloads)
 * licensing and distribution package information

Finally, the `single` directory contains small metadata-only JAR files, one
for each benchmark. These are intended to allow running individual benchmarks
in what we call _standalone mode_.

Standalone mode means executing a benchmark without the help of the launcher
from the main bundle and without module loading which relies on support for 
multiple class loaders. The benchmark harness is still used, but both the
harness and benchmark code are loaded using a single class loader. This is
useful in situations where using multiple class loaders makes the runtime too
convoluted, e.g., when benchmarking AOT-compiled code with GraalVM Native
Image.

Because the launcher is not used, the bundle needs to be manually extracted. 
The JAR files from the `single` directory can be then used to execute the
corresponding benchmark in standalone mode simply by running `java -jar <jar-file-path>`. 
The JAR file contains `benchmark.properties` describing on the
respective benchmark, and the JAR manifest contains a `Class-Path` attribute
that refers to all JAR files required by the benchmark, including `renaissance-harness` 
compiled with a matching version of Scala.
