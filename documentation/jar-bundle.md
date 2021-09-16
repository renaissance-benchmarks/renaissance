# Renaissance JAR bundle content

This document describes the structure of the JAR file with the benchmark
(e.g., `target/renaissance-gpl-0.13.0-2-SNAPSHOT.jar`).

Directly inside the JAR are classes from the `renaissance-core` subproject
that also contain the launcher. This also ensures that these classes are
always available when constructing a class loader with a default parent.

`META-INF/MANIFEST.MF` contains -- apart from standard information -- also
details about Git commit and Renaissance version it was built from
(see main `build.sbt` for details).

Because harness is loaded as a separate module, its JARs are stored inside
`renaissance-harness` subdirectory as standalone files.

Individual benchmark groups have separate subdirectory under `benchmarks`.
These contain all the required JARs for one benchmark group (including Scala
runtime libraries).

The list of JARs for each benchmark group is provided inside
`modules.properties`. Special group `renaissance-harness` contains list of JARs
for the harness.

The most complex file is `benchmarks.properties` that contains meta information
for each benchmark. This includes the following:

 * main class of the benchmark
 * supported version of JVM (min, max)
 * default number of iterations
 * licensing information
 * list of parameters and configurations (e.g., test for smaller workloads)
