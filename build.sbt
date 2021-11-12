import RenaissanceJmh.generateJmhWrapperBenchmarkClass
import org.renaissance.License
import org.renaissance.core.Launcher
import sbt.Def

import java.io.FileOutputStream
import java.nio.file.Files
import java.nio.file.Path
import java.nio.file.StandardCopyOption
import java.util.Properties
import scala.collection._
import scala.jdk.CollectionConverters.asScalaIteratorConverter

enablePlugins(GitBranchPrompt)

lazy val renaissanceCore = RootProject(uri("renaissance-core"))

lazy val renaissanceHarness = RootProject(uri("renaissance-harness"))

val renaissanceBenchmarks = for {
  // Hint: add .filter(Seq("group1", "group2").contains(_)) to compile
  // selected benchmark groups only (this can significantly speed-up
  // compilation/assembly when debugging the harness).
  dir <- file("benchmarks").list()
  benchDir = file("benchmarks") / dir
  if dir != null && (benchDir / "build.sbt").exists()
} yield {
  RootProject(benchDir)
}

val renaissanceModules = renaissanceBenchmarks :+ renaissanceHarness

val renaissanceProjects = renaissanceModules :+ renaissanceCore

// Do not assemble fat JARs in subprojects
assembly / aggregate := false

def flattenTasks[A](tasks: Seq[Def.Initialize[Task[A]]]): Def.Initialize[Task[Seq[A]]] =
  tasks.toList match {
    case Nil => Def.task { Nil }
    case x :: xs =>
      Def.taskDyn {
        flattenTasks(xs) map (x.value +: _)
      }
  }

def savePropertiesAsResource(props: Properties, file: File, comments: String): File = {
  file.getParentFile.mkdirs()

  val fos = new FileOutputStream(file)
  try {
    props.store(fos, comments)
    file
  } finally {
    fos.close()
  }
}

//
// Creates a task that collects the runtime dependency jars for
// the given project and returns a tuple as follows:
// (project name, relative path, runtime jars)
//
def defineProjectJarsCollectorTask(
  project: RootProject
): Def.Initialize[Task[(String, Path, Seq[File])]] =
  Def.task {
    val rootBase = baseDirectory.value.toPath
    val projectName = (project / name).value
    val projectBase = (project / baseDirectory).value.toPath
    val projectPath = rootBase.relativize(projectBase)
    val projectJars = (project / Runtime / dependencyClasspathAsJars).value.map(_.data)
    (projectName, projectPath, projectJars)
  }

//
// Creates a compound task that collects the runtime dependency jars
// for all given projects. This needs to be performed by aggregating
// results from per-project tasks.
//
def defineCompoundProjectJarsCollectorTask(projects: Array[RootProject]) =
  flattenTasks(projects.map { defineProjectJarsCollectorTask })

//
// Creates a task that generates the contents of the "modules.properties" file.
//
def defineModulesPropertiesGeneratorTask =
  Def.task {
    val logger = streams.value.log

    val modulesProps = new Properties
    defineCompoundProjectJarsCollectorTask(renaissanceModules).value.foreach { module =>
      val (moduleName, modulePath, moduleJars) = module
      val jarLine = moduleJars
        .map {
          // The path to a module JAR needs to use Unix-like paths (even on Windows).
          jar => modulePath.resolve(jar.getName).iterator().asScala.mkString("/")
        }
        .mkString(",")
      modulesProps.setProperty(moduleName, jarLine)
    }

    val modulesPropsFile = (Compile / resourceManaged).value / "modules.properties"

    logger.info(s"Writing $modulesPropsFile ...")
    Seq(savePropertiesAsResource(modulesProps, modulesPropsFile, "Module jars"))
  }

//
// Creates a task that generates the contents of the "benchmarks.properties" file.
//
def defineBenchmarksPropertiesGeneratorTask =
  Def.task {
    val logger = streams.value.log

    val benchmarksProps = new Properties
    defineCompoundProjectJarsCollectorTask(renaissanceBenchmarks).value.foreach { module =>
      val (moduleName, _, moduleJars) = module
      for (bench <- Benchmarks.listBenchmarks(moduleName, moduleJars, Some(logger))) {
        if (!nonGplOnly.value || bench.distro == License.MIT) {
          for ((k, v) <- bench.toMap) {
            benchmarksProps.setProperty(s"benchmark.${bench.name}.$k", v)
          }
        }
      }
    }

    val benchmarksPropsFile = (Compile / resourceManaged).value / "benchmarks.properties"

    logger.info(s"Writing $benchmarksPropsFile ...")
    Seq(savePropertiesAsResource(benchmarksProps, benchmarksPropsFile, "Benchmark details"))
  }

//
// Creates a task that copies the runtime jars of all benchmarks into
// resource output directory of the root project.
//
def defineCollectRuntimeJarsTask =
  Def.task {
    val logger = streams.value.log

    val outputDir = (Compile / resourceManaged).value.toPath
    defineCompoundProjectJarsCollectorTask(renaissanceModules).value.flatMap { module =>
      val (_, modulePath, moduleJars) = module

      logger.info(s"Collecting runtime dependencies for $modulePath ...")
      val moduleJarBase = Files.createDirectories(outputDir.resolve(modulePath))
      for (srcJar <- moduleJars) yield {
        val dstJar = moduleJarBase / srcJar.getName
        Files.copy(srcJar.toPath, dstJar, StandardCopyOption.REPLACE_EXISTING).toFile
      }
    }
  }

def defineRenaissanceAssemblyNameTask =
  Def.task {
    val bundle = if (nonGplOnly.value) "mit" else "gpl"
    "renaissance-" + bundle + "-" + (renaissanceCore / version).value + ".jar"
  }

addCommandAlias("renaissanceFormat", ";scalafmt;scalafmtSbt")

addCommandAlias("renaissanceFormatCheck", ";scalafmtCheck;scalafmtSbtCheck")

lazy val remoteDebug = SettingKey[Boolean](
  "remoteDebug",
  "Whether or not to enter a remote debugging session when running Renaissance."
)

lazy val nonGplOnly = SettingKey[Boolean](
  "nonGplOnly",
  "If set to true, then the distribution will not include GPL, EPL and MPL-licensed benchmarks."
)

val setupPrePush = taskKey[Unit](
  "Installs git pre-push hook."
)

def startupTransition(state: State): State = {
  "setupPrePush" :: state
}

// Installs a symlink to local pre-push hook.
def addLink(scriptFile: File, linkFile: File): Unit = {
  val linkPath = linkFile.toPath
  if (Files.isSymbolicLink(linkPath)) {
    // If the link can be read/executed, ensure that
    // it points to the desired pre-push hook script.
    val scriptPath = scriptFile.toPath
    if (Files.isExecutable(linkPath)) {
      if (Files.isSameFile(linkPath.toRealPath(), scriptPath)) {
        return
      }
    }

    // Otherwise just force a new relative symlink.
    val scriptRelPath = linkPath.getParent.relativize(scriptPath)
    println(s"Setting pre-push hook link to $scriptRelPath")
    Files.delete(linkPath)
    Files.createSymbolicLink(linkPath, scriptRelPath)

  } else {
    println("Not installing pre-push hook link over existing regular file!")
  }
}

lazy val renaissance: Project = {
  // Required for out of-the-box JDK16+ support in:
  // als, chi-square, gauss-mix, log-regression, naive-bayes, movie-lens
  // https://github.com/renaissance-benchmarks/renaissance/issues/241
  val addOpensPackages = List(
    "java.base/java.lang",
    "java.base/java.lang.invoke",
    "java.base/java.util",
    "java.base/java.nio",
    "java.base/sun.nio.ch",
    "java.management/sun.management",
    "java.management/sun.management.counter",
    "java.management/sun.management.counter.perf"
  )

  val p = Project("renaissance", file("."))
    .settings(
      name := "renaissance",
      version := (renaissanceCore / version).value,
      organization := (renaissanceCore / organization).value,
      crossPaths := false,
      autoScalaLibrary := false,
      remoteDebug := false,
      nonGplOnly := false,
      Compile / javaOptions ++= {
        if (remoteDebug.value) {
          Seq("-agentlib:jdwp=transport=dt_socket,server=y,suspend=y,address=8000")
        } else {
          Seq()
        }
      },
      Compile / resourceGenerators ++= Seq(
        defineModulesPropertiesGeneratorTask.taskValue,
        defineBenchmarksPropertiesGeneratorTask.taskValue,
        defineCollectRuntimeJarsTask.taskValue
      ),
      setupPrePush := addLink(file("tools") / "pre-push", file(".git") / "hooks" / "pre-push"),
      packageOptions := Seq(
        sbt.Package.ManifestAttributes(
          ("Specification-Title", "Renaissance Benchmark Suite"),
          // Consider Specification-Version to mark sets of active benchmarks
          ("Git-Head-Commit", git.gitHeadCommit.value.getOrElse("unknown")),
          ("Git-Head-Commit-Date", git.gitHeadCommitDate.value.getOrElse("unknown")),
          ("Git-Uncommitted-Changes", git.gitUncommittedChanges.value.toString),
          ("Add-Opens", addOpensPackages.mkString(" "))
        )
      ),
      // Configure fat JAR: specify its name, main(), do not run tests when
      // building it and raise error on file conflicts.
      assembly / assemblyJarName := defineRenaissanceAssemblyNameTask.value,
      assembly / mainClass := Some(classOf[Launcher].getName),
      assembly / test := {},
      assembly / assemblyMergeStrategy := {
        case PathList("META-INF", "MANIFEST.MF") => MergeStrategy.discard
        case _ => MergeStrategy.singleOrError
      },
      Global / cancelable := true,
      Global / onLoad := {
        val old = (Global / onLoad).value
        old.andThen(startupTransition)
      },
      run / fork := true
    )
    .dependsOn(
      renaissanceCore
    )

  renaissanceProjects.foldLeft(p)(_ aggregate _)
}

//
// This project generates a custom JMH wrapper for each Renaissance benchmark.
// Then, the project inserts JMH-specific functionality into the final JAR,
// which can then be run in a JMH-compliant way.
//
// Here are several technical details.
// First, to be able to generate the JMH wrapper classes, a project needs to "see"
// all the projects that define the benchmarks.
// Therefore, it was convenient to make the JMH project depend on the `renaissance` project.
// Second, the sbt-jmh plugins adds some (unnecessary) extra functionality,
// which forces this project to depend on the Scala library.
// This is why we cannot set `autoScalaLibrary` to `false` here.
// Third, the sbt-assembly plugin consequently automatically includes the Scala library
// into the fat JAR, which breaks classloading in the benchmarks that have
// a different Scala version (because the fat JAR is in the `AppClassLoader`).
// To amend this, we forcefully remove the Scala library classfiles from the fat JAR
// with a custom merge strategy -- this is fine, because the Scala library is only needed
// by the extra functionality that the sbt-jmh inserts into the artifact, and we don't
// need that anyway.

def defineJmhSourcesGeneratorTask =
  Def.task {
    val logger = streams.value.log

    val outputDir = (Compile / sourceManaged).value.toPath
    defineCompoundProjectJarsCollectorTask(renaissanceBenchmarks).value.flatMap { module =>
      val (moduleName, modulePath, moduleJars) = module
      for {
        bench <- Benchmarks.listBenchmarks(moduleName, moduleJars, Some(logger))
        if (!nonGplOnly.value || bench.distro == License.MIT) &&
          (!bench.groups.contains("dummy") || bench.name == "dummy-empty")
      } yield {
        logger.info(s"Generating JMH wrappers for $modulePath")
        generateJmhWrapperBenchmarkClass(bench, outputDir)
      }
    }
  }

lazy val renaissanceJmh = (project in file("renaissance-jmh"))
  .enablePlugins(JmhPlugin)
  .settings(
    name := "renaissance-jmh",
    version := (renaissance / version).value,
    organization := (renaissance / organization).value,
    nonGplOnly := (renaissance / nonGplOnly).value,
    assembly / mainClass := Some("org.openjdk.jmh.Main"),
    Compile / sourceGenerators += defineJmhSourcesGeneratorTask.taskValue,
    Jmh / assembly := ((Jmh / assembly) dependsOn (Jmh / compile)).value,
    assembly / assemblyMergeStrategy := {
      case PathList("scala", _*) =>
        MergeStrategy.discard
      case x =>
        val oldStrategy = (assembly / assemblyMergeStrategy).value
        oldStrategy(x)
    }
  )
  .dependsOn(
    renaissance
  )
