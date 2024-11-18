import org.renaissance.License
import sbt.Def
import sbt.Package
import sbt.Package.ManifestAttributes
import sbt.io.RegularFileFilter
import sbt.io.Using

import java.io.OutputStream
import java.nio.file.NoSuchFileException
import java.nio.file.Paths
import java.util.Properties
import java.util.jar.Attributes.Name
import java.util.jar.JarEntry
import java.util.jar.JarOutputStream
import java.util.jar.Manifest
import scala.collection.Seq
import scala.collection.immutable.ListSet

enablePlugins(GitVersioning)
enablePlugins(GitBranchPrompt)

//
// On startup, install 'tools/pre-push' as git pre-push hook.
//
val setupPrePush = taskKey[Unit]("Installs git pre-push hook.")
ThisBuild / setupPrePush := Utils.installSymlink(
  file("tools") / "pre-push",
  file(".git") / "hooks" / "pre-push",
  sLog.value
)

Global / onLoad := {
  val previousOnLoad = (Global / onLoad).value
  previousOnLoad.andThen(state => "setupPrePush" :: state)
}

// Support for distributions with different licenses.
//
val nonGplOnly = SettingKey[Boolean](
  "nonGplOnly",
  "If set to true, then the distribution will not include GPL, EPL and MPL-licensed benchmarks."
)

ThisBuild / nonGplOnly := false

//
// Make the build tasks cancelable.
//
Global / cancelable := true

//
// Determine project version using 'git describe'.
//
ThisBuild / git.useGitDescribe := true

//
// Compilation settings
//
val javaRelease = "11"
val scalaVersion212 = "2.12.20"
val scalaVersion213 = "2.13.15"
val scalaVersion3 = "3.3.4"

// Explicitly target a specific JDK release.
ThisBuild / javacOptions ++= Seq("--release", javaRelease)

// Use common organization name.
ThisBuild / organization := "org.renaissance"

lazy val commonSettingsNoScala = Seq(
  // Don't add Scala version to JAR name.
  crossPaths := false,
  // Don't include Scala library as dependency.
  autoScalaLibrary := false,
  // Override default Scala version to use Scala 3 harness.
  scalaVersion := scalaVersion3
)

lazy val commonSettingsScala212 = Seq(
  scalaVersion := scalaVersion212,
  // Scala 2.12 can only emit valid Java 8 classes.
  scalacOptions ++= Seq(s"-release:$javaRelease")
)

lazy val commonSettingsScala213 = Seq(
  scalaVersion := scalaVersion213,
  scalacOptions ++= Seq(s"-release:$javaRelease")
)

lazy val commonSettingsScala3 = Seq(
  scalaVersion := scalaVersion3,
  scalacOptions ++= Seq("-java-output-version", javaRelease),
  dependencyOverrides ++= Seq(
    // Force common version of Scala 2.13 library.
    "org.scala-lang" % "scala-library" % scalaVersion213
  )
)

//
// Other common settings
//

val modulesPropertiesName = "modules.properties"
val benchmarksPropertiesName = "benchmarks.properties"
val harnessMainClass = "org.renaissance.harness.RenaissanceSuite"
val launcherMainClass = "org.renaissance.core.Launcher"

addCommandAlias(
  "renaissanceFormat",
  ";renaissance/scalafmt;renaissance/scalafmtSbt"
)

addCommandAlias(
  "renaissanceFormatCheck",
  ";renaissance/scalafmtCheck;renaissance/scalafmtSbtCheck"
)

addCommandAlias("renaissancePackage", ";renaissance/package")
addCommandAlias("renaissanceJmhPackage", ";renaissanceJmh/package")

/**
 * Generates MANIFEST.MF attributes for top-level JAR files.
 *
 * Besides commonly found attributes, this also includes a collection of
 * Add-Opens specifiers required for out of-the-box support for JDK16+ in
 * various benchmarks: als, chi-square, gauss-mix, log-regression,
 * naive-bayes, movie-lens.
 *
 * @see See [[https://github.com/renaissance-benchmarks/renaissance/issues/241]]
 */
val generateManifestAttributesTask = Def.task {
  val addOpensPackages = Seq(
    "java.base/java.lang",
    "java.base/java.lang.invoke",
    "java.base/java.lang.reflect",
    "java.base/java.util",
    "java.base/java.nio",
    "java.base/sun.nio.ch",
    "java.management/sun.management",
    "java.management/sun.management.counter",
    "java.management/sun.management.counter.perf",
    // Required by Chronicle Map.
    "java.base/jdk.internal.ref",
    "jdk.compiler/com.sun.tools.javac.file"
  )

  Package.ManifestAttributes(
    ("Specification-Title", "Renaissance Benchmark Suite"),
    // Consider Specification-Version to mark sets of active benchmarks
    ("Git-Head-Commit", git.gitHeadCommit.value.getOrElse("unknown")),
    ("Git-Head-Commit-Date", git.gitHeadCommitDate.value.getOrElse("unknown")),
    ("Git-Uncommitted-Changes", git.gitUncommittedChanges.value.toString),
    ("Add-Opens", addOpensPackages.mkString(" ")),
    // Required by "org.lz4" % "lz4-java".
    ("Enable-Native-Access", "ALL-UNNAMED")
  )
}

//
// Subprojects
//

val arrowVersion = "18.0.0"
// ASM 9.7+ requires Java 11.
val asmVersion = "9.7.1"
// Caffeine 3.0+ requires Java 11.
val caffeineVersion = "3.1.8"
val commonsCompressVersion = "1.27.1"
val commonsIoVersion = "2.17.0"
val commonsLang3Version = "3.17.0"
val commonsMath3Version = "3.6.1"
val commonsTextVersion = "1.12.0"
val eclipseCollectionsVersion = "11.1.0"
val guavaVersion = "33.3.1-jre"
val jacksonVersion = "2.18.1"
val jakartaXmlBindVersion = "2.3.3"
val jerseyVersion = "2.45"
val jnaVersion = "5.15.0"
val nettyTomcatNativeVersion = "2.0.69.Final"
val nettyVersion = "4.1.114.Final"
val parquetVersion = "1.14.3"
val scalaCollectionCompatVersion = "2.12.0"
val scalaParallelCollectionsVersion = "1.0.4"
val scalaParserCombinatorsVersion = "2.4.0"
val slf4jVersion = "2.0.16"
val zstdJniVersion = "1.5.6-7"

lazy val renaissanceCore = (project in file("renaissance-core"))
  .settings(
    name := "renaissance-core",
    commonSettingsNoScala,
    Compile / mainClass := Some(launcherMainClass),
    Compile / javacOptions := Seq("--release", "8")
  )

val renaissanceHarnessCommonSettings = Seq(
  target := baseDirectory.value / "target" / name.value,
  moduleName := "renaissance-harness",
  libraryDependencies ++= Seq(
    "com.github.scopt" %% "scopt" % "4.1.0",
    "io.spray" %% "spray-json" % "1.3.6"
  ),
  Compile / mainClass := Some(harnessMainClass),
  Compile / javacOptions := Seq("--release", "8"),
  Compile / packageBin / packageOptions += generateManifestAttributesTask.value
)

lazy val renaissanceHarness3 = (project in file("renaissance-harness"))
  .settings(
    name := "renaissance-harness_3",
    commonSettingsScala3,
    renaissanceHarnessCommonSettings,
    scalacOptions := Seq("-java-output-version", "8")
  )
  .dependsOn(renaissanceCore % "provided")

lazy val renaissanceHarness213 = (project in file("renaissance-harness"))
  .settings(
    name := "renaissance-harness_2.13",
    commonSettingsScala213,
    renaissanceHarnessCommonSettings,
    scalacOptions := Seq("-release:8")
  )
  .dependsOn(renaissanceCore % "provided")

lazy val renaissanceHarness212 = (project in file("renaissance-harness"))
  .settings(
    name := "renaissance-harness_2.12",
    commonSettingsScala212,
    renaissanceHarnessCommonSettings,
    scalacOptions := Seq("-release:8"),
    libraryDependencies ++= Seq(
      // Needed to compile Scala 2.13 collections with Scala 2.12.
      "org.scala-lang.modules" %% "scala-collection-compat" % scalaCollectionCompatVersion
    )
  )
  .dependsOn(renaissanceCore % "provided")

//
// Benchmark subprojects. Each subproject can provide multiple benchmarks
// build around a common set of dependencies.
//

lazy val dummyBenchmarks = (project in file("benchmarks/dummy"))
  .settings(
    name := "dummy",
    commonSettingsNoScala
  )
  .dependsOn(renaissanceCore % "provided")

lazy val actorsAkkaBenchmarks = (project in file("benchmarks/actors-akka"))
  .settings(
    name := "actors-akka",
    commonSettingsScala3,
    libraryDependencies ++= Seq(
      // akka-actor 2.6.17+ supports Scala 2.12, 2.13, and 3 under Apache 2.0 license
      // akka-actor 2.7.0+ supports Scala 2.12, 2.13, and 3 under Business Source 1.1 license
      "com.typesafe.akka" %% "akka-actor" % "2.6.21"
    ),
    excludeDependencies ++= Seq(
      // Drop dependencies that are not needed for running on Java 11+.
      ExclusionRule("org.scala-lang.modules", "scala-java8-compat_3")
    )
  )
  .dependsOn(renaissanceCore % "provided")

lazy val actorsReactorsBenchmarks = (project in file("benchmarks/actors-reactors"))
  .settings(
    name := "actors-reactors",
    commonSettingsScala212
  )
  .dependsOn(
    renaissanceCore % "provided",
    ProjectRef(uri("benchmarks/actors-reactors/reactors"), "reactorsCommonJVM"),
    ProjectRef(uri("benchmarks/actors-reactors/reactors"), "reactorsCoreJVM")
  )

val sparkVersion = "3.5.3"

lazy val apacheSparkBenchmarks = (project in file("benchmarks/apache-spark"))
  .settings(
    name := "apache-spark",
    commonSettingsScala213,
    libraryDependencies ++= Seq(
      "org.apache.spark" %% "spark-core" % sparkVersion,
      "org.apache.spark" %% "spark-sql" % sparkVersion,
      "org.apache.spark" %% "spark-mllib" % sparkVersion
    ),
    // Exclude legacy logging libraries.
    excludeDependencies ++= Seq(
      // Replaced by the jcl-over-slf4j logging bridge.
      ExclusionRule("commons-logging", "commons-logging")
    ),
    // Override versions pulled in by dependencies.
    dependencyOverrides ++= Seq(
      // Force newer version of Hadoop (compatibility with IBM Semeru JDK builds).
      "org.apache.hadoop" % "hadoop-client-runtime" % "3.3.6",
      // Force common (newer) version of Netty packages.
      "io.netty" % "netty-all" % nettyVersion,
      // Force common (newer) version of Jackson packages.
      "com.fasterxml.jackson.datatype" % "jackson-datatype-jsr310" % jacksonVersion,
      "com.fasterxml.jackson.module" %% "jackson-module-scala" % jacksonVersion,
      // Force common (newer) version of Arrow packages.
      "org.apache.arrow" % "arrow-vector" % arrowVersion,
      "org.apache.arrow" % "arrow-memory-netty" % arrowVersion,
      // Force common (newer) version of Parquet packages.
      "org.apache.parquet" % "parquet-hadoop" % parquetVersion,
      // Force common (newer) version of Jersey packages.
      "org.glassfish.jersey.containers" % "jersey-container-servlet" % jerseyVersion,
      "org.glassfish.jersey.core" % "jersey-server" % jerseyVersion,
      "org.glassfish.jersey.inject" % "jersey-hk2" % jerseyVersion,
      // Force common versions of other dependencies.
      "com.github.luben" % "zstd-jni" % zstdJniVersion,
      "com.google.guava" % "guava" % guavaVersion,
      "commons-io" % "commons-io" % commonsIoVersion,
      "jakarta.xml.bind" % "jakarta.xml.bind-api" % jakartaXmlBindVersion,
      "org.apache.commons" % "commons-compress" % commonsCompressVersion,
      "org.apache.commons" % "commons-lang3" % commonsLang3Version,
      "org.apache.commons" % "commons-math3" % commonsMath3Version,
      "org.apache.commons" % "commons-text" % commonsTextVersion,
      "org.scala-lang.modules" %% "scala-collection-compat" % scalaCollectionCompatVersion,
      "org.scala-lang.modules" %% "scala-parallel-collections" % scalaParallelCollectionsVersion,
      "org.scala-lang.modules" %% "scala-parser-combinators" % scalaParserCombinatorsVersion,
      "org.slf4j" % "slf4j-api" % slf4jVersion,
      "org.slf4j" % "jcl-over-slf4j" % slf4jVersion,
      "org.slf4j" % "jul-to-slf4j" % slf4jVersion
    )
  )
  .dependsOn(renaissanceCore % "provided")

lazy val databaseBenchmarks = (project in file("benchmarks/database"))
  .settings(
    name := "database",
    commonSettingsScala3,
    libraryDependencies ++= Seq(
      "com.github.jnr" % "jnr-posix" % "3.1.20",
      "org.apache.commons" % "commons-math3" % commonsMath3Version,
      // Agrona 1.23+ requires Java 17.
      "org.agrona" % "agrona" % "1.22.0",
      // Database libraries.
      "org.mapdb" % "mapdb" % "3.1.0",
      "com.h2database" % "h2-mvstore" % "2.3.232",
      // Chronicle Map 3.25+ supports Java 21.
      "net.openhft" % "chronicle-map" % "3.26ea4",
      // Add simple binding to silence SLF4J warnings.
      "org.slf4j" % "slf4j-simple" % slf4jVersion,
      // Replacement for excluded "net.jpountz.lz4" % "lz4".
      "org.lz4" % "lz4-java" % "1.8.0"
    ),
    dependencyOverrides ++= Seq(
      // Force newer version of Chronicle modules.
      "net.openhft" % "chronicle-wire" % "2.26ea10",
      "net.openhft" % "posix" % "2.26ea3",
      // Force newer JNA to support more platforms/architectures.
      "net.java.dev.jna" % "jna-platform" % jnaVersion,
      // Force common (newer) version of ASM packages.
      "org.ow2.asm" % "asm-commons" % asmVersion,
      "org.ow2.asm" % "asm-util" % asmVersion,
      // Force common (newer) version of Eclipse collection packages.
      "org.eclipse.collections" % "eclipse-collections-forkjoin" % eclipseCollectionsVersion,
      // Force common versions of other dependencies.
      "com.google.guava" % "guava" % guavaVersion,
      "org.slf4j" % "slf4j-api" % slf4jVersion
    ),
    excludeDependencies ++= Seq(
      // Replaced by the "org.lz4" % "lz4-java".
      ExclusionRule("net.jpountz.lz4", "lz4")
    )
  )
  .dependsOn(renaissanceCore % "provided")

lazy val jdkConcurrentBenchmarks = (project in file("benchmarks/jdk-concurrent"))
  .settings(
    name := "jdk-concurrent",
    commonSettingsScala3,
    libraryDependencies ++= Seq(
      // Jenetics 6.3.0 is the last to support Java 11.
      // Jenetics 7.0.0 requires Java 17 and benchmark update.
      // Jenetics 8.0.0 requires Java 21 and benchmark update.
      "io.jenetics" % "jenetics" % "6.3.0"
    )
  )
  .dependsOn(renaissanceCore % "provided")

lazy val jdkStreamsBenchmarks = (project in file("benchmarks/jdk-streams"))
  .settings(
    name := "jdk-streams",
    commonSettingsScala3
  )
  .dependsOn(renaissanceCore % "provided")

val grpcVersion = "1.68.1"

lazy val neo4jBenchmarks = (project in file("benchmarks/neo4j"))
  .settings(
    name := "neo4j",
    commonSettingsScala213,
    libraryDependencies ++= Seq(
      // neo4j 4.4 supports Scala 2.12 and requires JDK11.
      // neo4j 5.x supports Scala 2.13 and requires JDK17.
      "org.neo4j" % "neo4j" % "5.25.1",
      // play-json 2.10.x requires SBT running on JDK11 to compile.
      "com.typesafe.play" %% "play-json" % "2.10.6"
    ),
    excludeDependencies ++= Seq(
      // Drop dependencies that are not really used by the benchmark.
      ExclusionRule("com.fasterxml.jackson.datatype", "jackson-datatype-jdk8")
    ),
    dependencyOverrides ++= Seq(
      // Force common (newer) version of Jackson packages.
      "com.fasterxml.jackson.datatype" % "jackson-datatype-jsr310" % jacksonVersion,
      "com.fasterxml.jackson.jaxrs" % "jackson-jaxrs-json-provider" % jacksonVersion,
      // Force newer JNA to support more platforms/architectures.
      "net.java.dev.jna" % "jna" % jnaVersion,
      // Force newer version of gRPC packages.
      "io.grpc" % "grpc-netty" % grpcVersion,
      "io.grpc" % "grpc-protobuf" % grpcVersion,
      "io.grpc" % "grpc-stub" % grpcVersion,
      // Force common (newer) version of Netty packages.
      "io.netty" % "netty-codec-http2" % nettyVersion,
      "io.netty" % "netty-handler-proxy" % nettyVersion,
      "io.netty" % "netty-transport-native-epoll" % nettyVersion,
      "io.netty" % "netty-transport-native-kqueue" % nettyVersion,
      "io.netty" % "netty-tcnative-classes" % nettyTomcatNativeVersion,
      // Force common (newer) version of Eclipse collection packages.
      "org.eclipse.collections" % "eclipse-collections" % eclipseCollectionsVersion,
      // Force common (newer) version of Arrow packages.
      "org.apache.arrow" % "flight-core" % arrowVersion,
      // Force common (newer) version of Parquet packages.
      "org.apache.parquet" % "parquet-hadoop" % parquetVersion,
      // Force common (newer) version of Jersey packages.
      "org.glassfish.jersey.containers" % "jersey-container-servlet" % jerseyVersion,
      "org.glassfish.jersey.core" % "jersey-server" % jerseyVersion,
      "org.glassfish.jersey.inject" % "jersey-hk2" % jerseyVersion,
      // Force common (newer) version of ASM packages.
      "org.ow2.asm" % "asm-util" % asmVersion,
      // Force common versions of other dependencies.
      "com.github.ben-manes.caffeine" % "caffeine" % caffeineVersion,
      "com.github.luben" % "zstd-jni" % zstdJniVersion,
      "commons-io" % "commons-io" % commonsIoVersion,
      "jakarta.xml.bind" % "jakarta.xml.bind-api" % jakartaXmlBindVersion,
      "org.apache.commons" % "commons-lang3" % commonsLang3Version,
      "org.apache.commons" % "commons-compress" % commonsCompressVersion,
      "org.apache.commons" % "commons-text" % commonsTextVersion,
      "org.slf4j" % "slf4j-nop" % slf4jVersion
    )
  )
  .dependsOn(renaissanceCore % "provided")

lazy val rxBenchmarks = (project in file("benchmarks/rx"))
  .settings(
    name := "rx",
    commonSettingsScala3,
    libraryDependencies ++= Seq(
      "io.reactivex.rxjava3" % "rxjava" % "3.1.9"
    )
  )
  .dependsOn(renaissanceCore % "provided")

lazy val scalaDottyBenchmarks = (project in file("benchmarks/scala-dotty"))
  .settings(
    name := "scala-dotty",
    commonSettingsScala3,
    libraryDependencies ++= Seq(
      // Version 3.1.2 was the last to compile with Scala 2.13.11. Version 3.1.3-RC2
      // broke compilation due to "Unsupported Scala 3 union in parameter value".
      // Compiling with Scala 3.1.0+ avoids compatibility issues.
      "org.scala-lang" % "scala3-compiler_3" % "3.3.4",
      // The following is required to compile the workload sources. Keep it last!
      "org.scala-lang" % "scala-compiler" % scalaVersion213 % Runtime
    ),
    excludeDependencies ++= Seq(
      // Drop dependencies that are not really used by the benchmark.
      ExclusionRule("net.java.dev.jna", "jna"),
      ExclusionRule("org.jline", "jline"),
      ExclusionRule("org.jline", "jline-reader"),
      ExclusionRule("org.jline", "jline-terminal"),
      ExclusionRule("org.jline", "jline-terminal-jna"),
      ExclusionRule("org.scala-sbt", "compiler-interface")
    )
  )
  .dependsOn(renaissanceCore % "provided")

lazy val scalaSatBenchmarks = (project in file("benchmarks/scala-sat"))
  .settings(
    name := "scala-sat",
    commonSettingsScala213
  )
  .dependsOn(
    renaissanceCore % "provided",
    RootProject(uri("benchmarks/scala-sat/scala-smtlib")),
    RootProject(uri("benchmarks/scala-sat/cafesat"))
  )

lazy val scalaStdlibBenchmarks = (project in file("benchmarks/scala-stdlib"))
  .settings(
    name := "scala-stdlib",
    commonSettingsScala3
  )
  .dependsOn(renaissanceCore % "provided")

lazy val scalaStmBenchmarks = (project in file("benchmarks/scala-stm"))
  .settings(
    name := "scala-stm",
    commonSettingsScala3,
    libraryDependencies := Seq(
      "org.scala-stm" %% "scala-stm" % "0.11.1"
    ),
    dependencyOverrides ++= Seq(
      // Force common version of Scala 3 library.
      "org.scala-lang" %% "scala3-library" % scalaVersion3
    )
  )
  .dependsOn(
    renaissanceCore % "provided",
    RootProject(uri("benchmarks/scala-stm/stmbench7"))
  )

val finagleVersion = "24.2.0"

lazy val twitterFinagleBenchmarks = (project in file("benchmarks/twitter-finagle"))
  .settings(
    name := "twitter-finagle",
    commonSettingsScala213,
    scalacOptions += "-feature",
    libraryDependencies := Seq(
      "com.google.guava" % "guava" % guavaVersion,
      "com.twitter" %% "finagle-http" % finagleVersion,
      "com.twitter" %% "finagle-stats" % finagleVersion,
      "com.twitter" %% "finagle-core" % finagleVersion,
      "com.twitter" %% "util-core" % finagleVersion,
      "org.scala-lang.modules" %% "scala-parallel-collections" % scalaParallelCollectionsVersion,
      // Add simple binding to silence SLF4J warnings.
      "org.slf4j" % "slf4j-simple" % slf4jVersion
    ),
    dependencyOverrides ++= Seq(
      // Force common (newer) version of Netty packages.
      "io.netty" % "netty-codec-http2" % nettyVersion,
      "io.netty" % "netty-handler-proxy" % nettyVersion,
      "io.netty" % "netty-resolver-dns" % nettyVersion,
      "io.netty" % "netty-transport-native-epoll" % nettyVersion,
      "io.netty" % "netty-tcnative-boringssl-static" % nettyTomcatNativeVersion,
      // Force common (newer) version of Jackson packages.
      "com.fasterxml.jackson.module" %% "jackson-module-scala" % jacksonVersion,
      // Force common versions of other dependencies.
      "com.github.ben-manes.caffeine" % "caffeine" % caffeineVersion,
      "com.github.luben" % "zstd-jni" % zstdJniVersion,
      "org.scala-lang.modules" %% "scala-collection-compat" % scalaCollectionCompatVersion,
      "org.scala-lang.modules" %% "scala-parser-combinators" % scalaParserCombinatorsVersion
    )
  )
  .dependsOn(renaissanceCore % "provided")

//
// Project collections.
//

/**
 * The [[renaissanceBenchmarks]] collection contains only projects that
 * provide benchmarks. It needs to be updated whenever a new benchmark
 * project is added (which is not that common).
 */
val renaissanceBenchmarks: Seq[Project] = Seq(
  dummyBenchmarks,
  actorsAkkaBenchmarks,
  actorsReactorsBenchmarks,
  apacheSparkBenchmarks,
  databaseBenchmarks,
  jdkConcurrentBenchmarks,
  jdkStreamsBenchmarks,
  neo4jBenchmarks,
  rxBenchmarks,
  scalaDottyBenchmarks,
  scalaSatBenchmarks,
  scalaStdlibBenchmarks,
  scalaStmBenchmarks,
  twitterFinagleBenchmarks
)

/**
 * The [[aggregateProjects]] collection does not include [[renaissanceCore]],
 * because the build (meta) project depends on it and running the aggregate
 * 'clean' task on the [[renaissance]] (root) project would break the build.
 */
val aggregateProjects =
  renaissanceBenchmarks :+ renaissanceHarness3 :+ renaissanceHarness213 :+ renaissanceHarness212

/**
 * The [[renaissanceModules]] collection contains projects that represent
 * modules, i.e., they will have an entry in the 'modules.properties' file
 * and the final fat JAR will contain a directory with their dependencies.
 */
val renaissanceModules = aggregateProjects :+ renaissanceCore

/**
 * Creates a task that collects the runtime dependency jars for the given
 * projects. For each project, we need to create a separate tasks to query
 * the project settings, because these can be only evaluated in a task. The
 * obvious approach of subjecting the input sequence to a mapping function
 * cannot be used in SBT at this level.
 *
 * The task produces a sequence of tuples with the following structure:
 * (project name, runtime jars, scala version)
 */
def collectModulesDetailsTask(projects: Seq[Project]) =
  Tasks.collect[(String, Seq[File], String)](projects.map { project =>
    // Create a task to produce output tuple for a specific project.
    Def.task {
      val projectName = (project / name).value
      val projectJars = (project / Runtime / dependencyClasspathAsJars).value.map(_.data)
      val projectScala = CrossVersion.binaryScalaVersion((project / scalaVersion).value)
      (projectName, projectJars, projectScala)
    }
  })

//
// Tasks related to generating 'modules.properties'.
// This makes them easier to run manually (for debugging purposes).
//

lazy val modulesWithDependencies = taskKey[Seq[(String, Seq[(File, String)])]](
  "Collects runtime dependency jars for Renaissance modules"
)

renaissance / modulesWithDependencies := mapModuleJarsToAssemblyEntries(
  collectModulesDetailsTask(renaissanceModules).value
)

lazy val generateModulesProperties = inputKey[Seq[File]](
  "Collects module metadata and stores it in a properties file of given name."
)

renaissance / generateModulesProperties := {
  import complete.DefaultParsers._
  val outputName = trimmed(OptSpace ~> StringBasic).parsed
  val outputFile = (Compile / resourceManaged).value / outputName
  val properties = makeModulesProperties(modulesWithDependencies.value)
  Seq(Utils.storeProperties(properties, "Module jars", outputFile, Some(sLog.value)))
}

def makeModulesProperties(modules: Seq[(String, Seq[(File, String)])]) = {
  // Collect metadata into Properties, mutating the initial instance.
  modules.foldLeft(new Properties) {
    case (props, (module, dependencies)) =>
      val jarLine = dependencies.map { case (_, jarEntry) => jarEntry }.mkString(",")
      props.setProperty(module, jarLine)
      props
  }
}

//
// Tasks related to generating 'benchmarks.properties'.
// This makes them easier to run manually (for debugging purposes).
//

lazy val benchmarkDescriptors = taskKey[Seq[BenchmarkInfo]](
  "Produces a collection of benchmark descriptors for all benchmarks."
)

renaissance / benchmarkDescriptors := collectModulesDetailsTask(renaissanceBenchmarks).value
  .flatMap {
    // Find benchmarks in each benchmark module and return the descriptors.
    case (moduleName, moduleJars, scalaVersion) =>
      Benchmarks.listBenchmarks(moduleName, moduleJars, scalaVersion, None)
  }

lazy val distroBenchmarkDescriptors = taskKey[Seq[BenchmarkInfo]](
  "Produces a collection of benchmark descriptors. " +
    "Includes only benchmarks matching the currently configured distribution."
)

renaissance / distroBenchmarkDescriptors := benchmarkDescriptors.value.filter(b =>
  !nonGplOnly.value || b.distro == License.MIT
)

lazy val distroRealBenchmarkDescriptors = taskKey[Seq[BenchmarkInfo]](
  "Produces a collection of benchmark descriptors. " +
    "Includes only benchmarks matching the currently configured distribution, " +
    "but excludes dummy benchmarks (with the exception of dummy-empty)."
)

renaissance / distroRealBenchmarkDescriptors := distroBenchmarkDescriptors.value.filter(b =>
  !b.groups.contains("dummy") || b.name == "dummy-empty"
)

lazy val generateBenchmarksProperties = inputKey[Seq[File]](
  "Collects benchmark metadata and stores it in a properties file of given name." +
    "Includes only benchmarks matching the currently configured distribution."
)

renaissance / generateBenchmarksProperties := {
  import complete.DefaultParsers._
  val outputName = trimmed(OptSpace ~> StringBasic).parsed
  val outputFile = (Compile / resourceManaged).value / outputName
  val properties = makeBenchmarksProperties(distroBenchmarkDescriptors.value)
  Seq(Utils.storeProperties(properties, "Benchmark details", outputFile, Some(sLog.value)))
}

def makeBenchmarksProperties(benchmarks: Seq[BenchmarkInfo]) = {
  //
  // Map benchmark property names into global name space and collect
  // metadata for all benchmarks into a single Properties instance.
  //
  benchmarks.foldLeft(new Properties) {
    case (props, bench) =>
      bench.toMap.foreach {
        case (k, v) =>
          props.setProperty(s"benchmark.${bench.name}.$k", v)
      }
      props
  }
}

def mapModuleJarsToAssemblyEntries(modulesDetails: Seq[(String, Seq[File], String)]) = {
  //
  // Convert a collection of modules referencing dependency jars into
  // a collection of dependency jars referencing modules that use them.
  //
  // (m1, (j1, j2)), (m2, (j1, j3)), ... =>
  // (m1, j1), (m1, j2), (m2, j1), (m2, j3), ... ->
  // j1 -> ((m1, j1), (m2, j1)), j2 -> ((m1, j2)), j3 -> ((m2, j3)), ...
  //
  val jarModules: Map[String, Seq[(String, File)]] = modulesDetails
    .flatMap {
      case (module, jars, _) => jars.map { jar => (module, jar) }
    }
    .groupBy { case (_, jar) => jar.getName }

  //
  // Map each module jar to an entry in the assembly.
  // Jars used by multiple modules go into shared directory.
  // Jars used by a single module go into module-specific directory.
  //
  val shared = Paths.get("shared")
  val unique = Paths.get("unique")

  val jarEntries = jarModules.flatMap {
    case (jarBaseName, modules) =>
      modules.map {
        case (name, jarPath) =>
          val entryDir = if (modules.length < 2) unique.resolve(name) else shared
          val entryPath = entryDir.resolve(jarBaseName)
          // Jar entry needs to use Unix path separator (even on Windows).
          jarPath -> Utils.asUnixPath(entryPath)
      }
  }

  //
  // Associate module jars with assembly jar entries
  // in the original collection (grouped by module).
  // This is basically a join on the jar source path.
  //
  modulesDetails.map {
    case (name, jars, _) =>
      name -> jars.map(srcJar => (srcJar, jarEntries(srcJar)))
  }
}

def mapModuleDependencyJarsToAssemblyTask(modules: Seq[Project]) =
  Def.task[Seq[(File, String)]] {
    val log = sLog.value
    val targetDir = (Compile / target).value

    val modulesDetails = collectModulesDetailsTask(modules).value
    mapModuleJarsToAssemblyEntries(modulesDetails).flatMap(_._2).distinct.map { entry =>
      // Use patched "hadoop-client-api" to allow running on Java 23+.
      if (entry._1.name.startsWith("hadoop-client-api")) {
        remapHadoopClientApiJarEntry(entry, targetDir, log)
      } else {
        entry
      }
    }
  }

def remapHadoopClientApiJarEntry(entry: (File, String), targetDir: File, log: Logger) = {
  val originalJar = entry._1
  val patchedJar = targetDir / "patched" / originalJar.name

  if (patchedJar.exists()) {
    log.info(s"Remapping Hadoop Client API to patched jar in $patchedJar")
    (patchedJar, entry._2)
  } else {
    log.error(s"Could not find patched Hadoop Client API jar in $patchedJar")

    // Throw an exception here to stop the build. This is necessary, because
    // the SBT assembly task does not check if the source files exist when
    // producing the final JAR file.
    throw new NoSuchFileException(patchedJar.toString)
  }
}

/**
 * Generates assembly mappings for all class files on the given classpath.
 * The class directory hierarchy is mapped to the root of the assembly so
 * that the classes are directly available to the JVM.
 */
def mapClassesToAssemblyTask(classpath: Classpath) =
  Def.task[Seq[(File, String)]] {
    classpath.map(_.data).filter(_.isDirectory).flatMap { dir =>
      //
      // For all files below the class path directory, the destination
      // in the package is the relative part of the path (with respect
      // to the classpath directory).
      //
      val filePaths = (dir ** (-DirectoryFilter)).get()
      filePaths.pair(_.relativeTo(dir)).map {
        // Jar entry needs to use Unix path separator (even on Windows).
        case (src, rel) => src -> Utils.asUnixPath(rel.toPath)
      }
    }
  }

//
// Tasks related to generating patched Hadoop Client API jar.
//

lazy val generatePatchedHadoopClientApiJar = taskKey[Seq[File]](
  "Generates a patched Hadoop Client API jar which modifies the 'UserGroupInformation' class " +
    "to avoid calling deprecated Java Security API. This allows using Spark with Java 23+ " +
    "without having to specify the -Djava.security.manager=allow on the command line, which " +
    "allows running with GraalVM Native Image."
)

def generatePatchedHadoopClientApiJarTask = {
  Def.task {
    val log = sLog.value
    val targetDir = (Compile / target).value / "patched"

    val dependencyJars = (apacheSparkBenchmarks / Runtime / dependencyClasspathAsJars).value
    dependencyJars.map(_.data).filter(f => f.name.startsWith("hadoop-client-api")).map {
      originalJar =>
        val patchedJar = targetDir / originalJar.name
        if (!patchedJar.exists()) {
          log.info(s"Creating patched Hadoop Client API jar in $patchedJar")
          IO.createDirectory(targetDir)

          val temporaryJar = patchedJar.getParentFile / (patchedJar.name + ".tmp")
          if (Hadoop.patchClientApiJar(originalJar, temporaryJar, log)) {
            IO.move(temporaryJar, patchedJar)
            patchedJar
          } else {
            log.error(s"Failed to create patched Hadoop Client API jar in $patchedJar")
            null
          }
        } else {
          log.info(s"Found patched Hadoop Client API jar in $patchedJar")
          patchedJar
        }
    }
  }
}

//
// Tasks related to generating metadata-only jars for benchmarks.
// This makes them easier to run manually (for debugging purposes).
//

lazy val generateStandaloneJars = taskKey[Seq[File]](
  "Generates metadata-only jars for standalone benchmark execution." +
    "Includes only benchmarks matching the currently configured distribution, " +
    "but excludes dummy benchmarks (with the exception of dummy-empty)."
)

renaissance / generateStandaloneJars := {
  val outputDir = (Compile / resourceManaged).value / "single"

  sLog.value.debug(s"Deleting standalone jars in $outputDir")
  IO.delete(outputDir)

  val modulesWithDeps = modulesWithDependencies.value.toMap
  val basePkgOptions = (Compile / packageBin / packageOptions).value

  sLog.value.info(s"Creating standalone jars in $outputDir")
  distroRealBenchmarkDescriptors.value.map { bench =>
    sLog.value.debug(s"Generating standalone JAR for ${bench.name}")

    // Collect all dependencies, together with core and harness packages.
    val deps = modulesWithDeps(bench.module) ++ modulesWithDeps(
      s"renaissance-harness_${bench.scalaVersion}"
    ) ++ modulesWithDeps("renaissance-core")

    // Paths in the manifest are unix-style. Preserve insertion order!
    val jars = deps.map { case (_, entry) => s"../$entry" }.to[ListSet]

    //
    // Copy manifest attributes and override the 'Main-Class' attribute to
    // refer to the harness main class (instead of the launcher). Set the
    // 'Class-Path' attribute to refer to all the dependencies used by this
    // benchmark, and set the 'Renaissance-Use-Modules' attribute to tell the
    // harness to avoid using modules.
    //
    val pkgOptions = basePkgOptions :+ Package.ManifestAttributes(
      Name.MANIFEST_VERSION -> "1.0",
      Name.MAIN_CLASS -> harnessMainClass,
      Name.CLASS_PATH -> jars.mkString(" "),
      new Name("Renaissance-Use-Modules") -> false.toString
    )

    val manifest = createPackageManifest(pkgOptions)
    val properties = makeBenchmarksProperties(Seq(bench))
    val outputJar = outputDir / s"${bench.name}.jar"
    createStandaloneJar(manifest, properties, outputJar, Some(sLog.value))
  }
}

def createPackageManifest(packageOptions: Seq[PackageOption]) = {
  packageOptions.foldLeft(new Manifest) {
    // Collect manifest attributes.
    case (manifest, ManifestAttributes(attributes @ _*)) =>
      attributes.foldLeft(manifest.getMainAttributes) {
        case (attrs, (name, value)) =>
          attrs.put(name, value)
          attrs
      }
      manifest

    // Ignore other package options.
    case (manifest, _) =>
      manifest
  }
}

/**
 * Creates a JAR containing only the manifest and the properties
 * file with the metadata of a single benchmark. Such a JAR can be
 * used to execute a single benchmark without module loading.
 */
def createStandaloneJar(
  manifest: Manifest,
  metadata: Properties,
  outputJar: File,
  maybeLog: Option[Logger]
): File = {
  maybeLog.foreach { log => log.debug(s"Writing $outputJar ...") }

  // Wrapper for JarOutputStream with manifest.
  val jarOutputStream = Using.wrap((os: OutputStream) => new JarOutputStream(os, manifest))

  // Create leading directories.
  Option(outputJar.getParentFile).foreach { dir => IO.createDirectory(dir) }

  // Write the jar file.
  Using.fileOutputStream(append = false)(outputJar) { fos =>
    jarOutputStream(fos) { jos =>
      // Store benchmark properties without intermediate file.
      jos.putNextEntry(new JarEntry(benchmarksPropertiesName))
      metadata.store(jos, "Benchmark metadata")
      jos.closeEntry()
    }
  }

  outputJar
}

/**
 * This is the root project. The tasks that generate metadata files and
 * the final bundle depend on [[renaissanceModules]] which contains the
 * harness and the benchmark projects. The evaluation of those tasks will
 * trigger the compilation of the modules.
 */
lazy val renaissance = (project in file("."))
  .settings(
    commonSettingsNoScala,
    name := "renaissance",
    // Reflect the distribution license in the package name.
    moduleName := name.value + "-" + (if (nonGplOnly.value) "mit" else "gpl"),
    generatePatchedHadoopClientApiJar := generatePatchedHadoopClientApiJarTask.value,
    inConfig(Compile)(
      Seq(
        // The main class for the JAR is the Launcher from the core package.
        mainClass := (renaissanceCore / Compile / mainClass).value,
        // Generate module and benchmark metadata and metadata-only jars.
        resourceGenerators ++= Seq(
          generateModulesProperties.toTask(modulesPropertiesName).taskValue,
          generateBenchmarksProperties.toTask(benchmarksPropertiesName).taskValue,
          generateStandaloneJars.taskValue
        ),
        // Set additional manifest attributes, especially Add-Opens.
        packageBin / packageOptions += generateManifestAttributesTask.value,
        // Include core classes directly in the output JAR file.
        packageBin / mappings ++= Def.taskDyn {
          val classpath = internalDependencyClasspath.value
          mapClassesToAssemblyTask(classpath)
        }.value,
        // Include dependency JAR files in the output JAR.
        //
        // Also remaps the Hadoop Client API jar to a patched version. We use task dependency
        // to ensure that the patched jar is produced before the mappings. Resource generators
        // are useless, because they run concurrently with the mapping tasks. This would not
        // be a problem if the mapping source files were actually checked for existence when
        // creating the final JAR.
        packageBin / mappings ++= mapModuleDependencyJarsToAssemblyTask(
          renaissanceModules
        ).dependsOn(generatePatchedHadoopClientApiJar).value
      )
    )
  )
  // The bundle directly depends only on the 'renaissance-core' classes.
  .dependsOn(renaissanceCore)
  // Aggregate other modules for selected tasks.
  .aggregate(aggregateProjects.map { _.project }: _*)
  .settings(
    aggregate := false,
    clean / aggregate := true,
    scalafmt / aggregate := true,
    update / aggregate := true
  )

//
// JMH support
//

val jmhVersion = "1.37"

//
// Tasks related to generating JMH wrappers jars for benchmarks.
// This makes them easier to run manually (for debugging purposes).
//

lazy val generateJmhWrappers = taskKey[Seq[File]](
  "Generates wrappers for benchmark execution under JMH." +
    "Includes only benchmarks matching the currently configured distribution, " +
    "but excludes dummy benchmarks (with the exception of dummy-empty)."
)

/**
 * Generates JMH wrappers for Renaissance benchmarks. Each wrapper is derived
 * from a common base class and includes just the benchmark-specific information
 * needed to run the benchmark under JMH. The task returns a collection of
 * generated source files.
 */
renaissanceJmhWrappers / generateJmhWrappers := {
  val outputDir = (Compile / sourceManaged).value

  // Delete all subdirectories in the output directory.
  sLog.value.debug(s"Deleting JMH wrappers in $outputDir")
  IO.delete(outputDir)

  sLog.value.info(s"Generating JMH wrappers in $outputDir")
  distroRealBenchmarkDescriptors.value.map { bench =>
    sLog.value.debug(s"Generating JMH wrapper for ${bench.name}")
    RenaissanceJmh.generateJmhWrapperBenchmarkClass(bench, outputDir.toPath)
  }
}

/**
 * Generates JMH sources and resources for the generated benchmark wrappers.
 * Because the JMH generator produces sources and resources at the same time,
 * the task returns two corresponding file collections.
 */
def generateJmhSourcesResourcesTask(wrappers: Project) =
  Def.task[(Seq[File], Seq[File])] {
    val inputBytecodeDir = (wrappers / Compile / classDirectory).value
    val outputSourceDir = (Compile / sourceManaged).value
    val outputResourceDir = (Compile / resourceManaged).value

    val jmhMainClass = "org.openjdk.jmh.generators.bytecode.JmhBytecodeGenerator"
    val jmhClasspath = (Compile / dependencyClasspath).value.map(_.data)
    val jmhOptions = Seq(inputBytecodeDir, outputSourceDir, outputResourceDir).map(_.toString)

    sLog.value.debug(
      s"Running JMH generator...\n\toptions: $jmhOptions\n\tclasspath: $jmhClasspath"
    )
    val sbtRun = new Run(scalaInstance.value, true, taskTemporaryDirectory.value)
    sbtRun.run(jmhMainClass, jmhClasspath, jmhOptions, sLog.value).get

    // Return sources and resources separately.
    val sourceFiles = (outputSourceDir ** RegularFileFilter).get
    val resourceFiles = (outputResourceDir ** RegularFileFilter).get
    (sourceFiles, resourceFiles)
  }

/**
 * Generates assembly mappings for the contents of JAR files on the given
 * classpath. Each JAR file is extracted to a separate directory and all
 * files from that directory (except the manifest) are mapped to the root
 * of the final assembly.
 */
def mapJarContentsToAssemblyTask(classpath: Classpath) =
  Def.task[Seq[(File, String)]] {
    val log = sLog.value

    val outputDir = target.value / "jar_contents"
    classpath.map(_.data).filter(_.isFile).flatMap { jar =>
      // Extract the JAR file.
      val jarOutputDir = outputDir / jar.getName
      IO.delete(jarOutputDir)
      log.debug(s"Extracting $jar => $jarOutputDir")
      IO.unzip(jar, jarOutputDir, "*", preserveLastModified = true)

      // Get all files except the manifest.
      val allFiles = jarOutputDir ** RegularFileFilter
      val manifestFile = jarOutputDir / "META-INF" / "MANIFEST.MF"
      val includedFiles = allFiles --- manifestFile

      // Map the files to the output JAR.
      includedFiles
        .pair(_.relativeTo(jarOutputDir))
        .map {
          // Jar entry needs to use Unix path separator (even on Windows).
          case (src, rel) => src -> Utils.asUnixPath(rel.toPath)
        }
    }
  }

/**
 * This project generates JMH wrappers for Renaissance benchmarks. The
 * compiled wrappers are used by the [[renaissanceJmh]] project below.
 */
lazy val renaissanceJmhWrappers = (project in file("renaissance-jmh/wrappers"))
  .settings(
    name := "renaissance-jmh-wrappers",
    commonSettingsNoScala,
    libraryDependencies := Seq(
      "org.openjdk.jmh" % "jmh-core" % jmhVersion
    ),
    Compile / sourceGenerators += generateJmhWrappers.taskValue
  )
  // We need the module and benchmark metadata in addition to core classes.
  .dependsOn(renaissance)

/**
 * This project provides support for running Renaissance under JMH. It
 * generates JMH benchmarks and resources using the JMH wrappers from the
 * [[renaissanceJmhWrappers]] project above. The final bundle then needs
 * to include all the generated classes and JMH classes directly (including
 * its dependencies), along with the benchmark dependencies as JAR files.
 */
lazy val renaissanceJmh = (project in file("renaissance-jmh"))
  .settings(
    name := "renaissance-jmh",
    commonSettingsNoScala,
    libraryDependencies := Seq(
      "org.openjdk.jmh" % "jmh-generator-bytecode" % jmhVersion,
      "org.openjdk.jmh" % "jmh-generator-reflection" % jmhVersion
    ),
    generatePatchedHadoopClientApiJar := generatePatchedHadoopClientApiJarTask.value,
    inConfig(Compile)(
      Seq(
        // Split result from the JMH generator task between sources and resources.
        sourceGenerators += Def.task {
          generateJmhSourcesResourcesTask(renaissanceJmhWrappers).value._1
        }.taskValue,
        resourceGenerators += Def.task {
          generateJmhSourcesResourcesTask(renaissanceJmhWrappers).value._2
        }.taskValue,
        // The main class for the JAR is the JMH launcher.
        mainClass := Some("org.openjdk.jmh.Main"),
        // Generate benchmark metadata used by the launcher/harness.
        packageBin / packageOptions += generateManifestAttributesTask.value,
        // Include classes from internal dependencies directly.
        packageBin / mappings ++= Def.taskDyn {
          val classpath = internalDependencyClasspath.value
          mapClassesToAssemblyTask(classpath)
        }.value,
        // Include the contents of JAR files of compile dependencies.
        packageBin / mappings ++= Def.taskDyn {
          val classpath = (renaissanceJmhWrappers / Compile / externalDependencyClasspath).value
          mapJarContentsToAssemblyTask(classpath)
        }.value,
        // Include benchmark dependency JAR files in the output JAR.
        packageBin / mappings ++= mapModuleDependencyJarsToAssemblyTask(
          renaissanceModules
        ).dependsOn(generatePatchedHadoopClientApiJar).value
      )
    )
  )
  .dependsOn(renaissanceJmhWrappers)
