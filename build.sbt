import java.net.URLClassLoader
import java.nio.charset.StandardCharsets
import java.nio.file.Files
import java.nio.file.StandardCopyOption
import java.util.jar.JarFile
import java.util.regex.Pattern

import org.renaissance.Launcher
import org.renaissance.License
import org.renaissance.RenaissanceBenchmark

import scala.collection._

val renaissanceScalaVersion = "2.12.8"

lazy val renaissanceCore = RootProject(uri("renaissance-core"))

lazy val renaissanceHarness = RootProject(uri("renaissance-harness"))

val benchmarkProjects = for {
  // Hint: add .filter(_ == "group") to compile with selected group only
  // (can significantly speed-up compilation/assembly when debugging harness).
  dir <- file("benchmarks").list()
  if dir != null && file("benchmarks/" + dir + "/build.sbt").exists()
} yield {
  RootProject(uri("benchmarks/" + dir))
}

val subProjects = benchmarkProjects :+ renaissanceHarness

val allProjects = subProjects :+ renaissanceCore

// Do not assemble fat JARs in subprojects
aggregate in assembly := false

def flattenTasks[A](tasks: Seq[Def.Initialize[Task[A]]]): Def.Initialize[Task[Seq[A]]] =
  tasks.toList match {
    case Nil => Def.task { Nil }
    case x :: xs =>
      Def.taskDyn {
        flattenTasks(xs) map (x.value +: _)
      }
  }

def logBenchmark(b: BenchmarkInfo, logger: Logger) = {
  logger.info(s"class: ${b.className}")
  logger.info(s"\tbenchmark: ${b.group}/${b.name}")
  logger.info(s"\tlicensing: ${b.printableLicenses} => ${b.distro}")
  logger.info(s"\trepetitions: ${b.repetitions}")
  logger.info(s"\tsummary: ${b.summary}")
}

// Return tuples with (name, distro license, all licenses, description and default repetitions)
def listBenchmarks(classpath: Seq[File], logger: Option[Logger]): Seq[BenchmarkInfo] = {
  //
  // Load the benchmark base class and create a class loader for the project
  // with the class loader of the base class as its parent. This will allow
  // us to use core classes here.
  //
  val benchBase = classOf[RenaissanceBenchmark]
  val urls = classpath.map(_.toURI.toURL).toArray
  val loader = new URLClassLoader(urls, benchBase.getClassLoader)
  val excludePattern = Pattern.compile("org[.]renaissance(|[.]harness|[.]util)")

  //
  // Scan all JAR files for classes in the org.renaissance package implementing
  // the benchmark interface and collect metadata from class annotations.
  //
  val result = new mutable.ArrayBuffer[BenchmarkInfo]
  for (jarFile <- classpath.map(jar => new JarFile(jar))) {
    for (entry <- JavaConverters.enumerationAsScalaIterator(jarFile.entries())) {
      if (entry.getName.startsWith("org/renaissance") && entry.getName.endsWith(".class")) {
        val benchClassName = entry.getName
          .substring(0, entry.getName.length - ".class".length)
          .replace("/", ".")
        val clazz = loader.loadClass(benchClassName)

        val isEligible =
          !excludePattern.matcher(clazz.getPackage.getName).matches() &&
            benchBase.isAssignableFrom(clazz)
        if (isEligible) {
          // Print info to see what benchmarks are picked up by the build.
          val benchClass = clazz.asSubclass(benchBase)
          val info = new BenchmarkInfo(benchClass)
          if (logger.nonEmpty) logBenchmark(info, logger.get)

          result += info
        }
      }
    }
  }

  result
}

def projectJars = Def.taskDyn {
  // Each generated task returns tuple of
  // (project path, all JAR files, all JAR files without renaissance core JAR*)
  // * because renaissance core classes are shared across all benchmarks
  val projectJarTasks = for {
    p <- subProjects
  } yield
    Def.task {
      val mainJar = (packageBin in (p, Compile)).value
      val coreJar = (packageBin in (renaissanceCore, Runtime)).value
      val depJars = (dependencyClasspath in (p, Compile)).value.map(_.data).filter(_.isFile)
      val loadedJarFiles = mainJar +: depJars
      val allJars = mainJar +: coreJar +: depJars
      val project = p.asInstanceOf[RootProject].build.getPath
      val jarFiles = for (jar <- allJars) yield {
        val dest = (resourceManaged in Compile).value / project / jar.getName
        dest.getParentFile.mkdirs()
        Files.copy(jar.toPath, dest.toPath, StandardCopyOption.REPLACE_EXISTING)
        dest
      }
      (project, jarFiles, loadedJarFiles)
    }
  flattenTasks(projectJarTasks)
}

def jarsAndListGenerator = Def.taskDyn {
  val nonGpl = nonGplOnly.value
  val logger = streams.value.log

  // Flatten list and create a groups-jars file and the benchmark-details file.
  projectJars.map { groupJars =>
    // Add the benchmarks from the different project groups.
    val jarListContent = new StringBuilder
    val benchDetails = new java.util.Properties

    for ((project, allJars, loadedJars) <- groupJars) {
      val jarLine = loadedJars.map(jar => project + "/" + jar.getName).mkString(",")
      val projectShort = project.stripPrefix("benchmarks/")
      jarListContent.append(projectShort).append("=").append(jarLine).append("\n")

      // Scan project jars for benchmarks and fill the property file.
      for (benchInfo <- listBenchmarks(allJars, Some(logger))) {
        if (!nonGpl || benchInfo.distro() == License.MIT) {
          for ((k, v) <- benchInfo.toMap()) {
            benchDetails.setProperty(s"benchmark.${benchInfo.name}.$k", v);
          }
        }
      }
    }

    val jarListFile = (resourceManaged in Compile).value / "groups-jars.txt"
    IO.write(jarListFile, jarListContent.toString, StandardCharsets.UTF_8)

    val benchDetailsFile = (resourceManaged in Compile).value / "benchmark-details.properties"
    val benchDetailsStream = new java.io.FileOutputStream(benchDetailsFile)
    benchDetails.store(benchDetailsStream, "Benchmark details")

    benchDetailsFile +: jarListFile +: groupJars.flatMap {
      case (_, jars, _) => jars
    }
  }
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
    println(s"Setting pre-push hook link to ${scriptRelPath}")
    Files.delete(linkPath)
    Files.createSymbolicLink(linkPath, scriptRelPath)

  } else {
    println("Not installing pre-push hook link over existing regular file!")
  }
}

lazy val renaissance: Project = {
  val p = Project("renaissance", file("."))
    .settings(
      name := "renaissance",
      version := (version in renaissanceCore).value,
      organization := (organization in renaissanceCore).value,
      crossPaths := false,
      autoScalaLibrary := false,
      resourceGenerators in Compile += jarsAndListGenerator.taskValue,
      fork in run := true,
      cancelable in Global := true,
      remoteDebug := false,
      nonGplOnly := false,
      setupPrePush := addLink(file("tools") / "pre-push", file(".git") / "hooks" / "pre-push"),
      packageOptions := Seq(
        sbt.Package.ManifestAttributes(
          ("Specification-Title", "Renaissance Benchmark Suite")
          // Consider Specification-Version to mark sets of active benchmarks
        )
      ),
      // Configure fat JAR: specify its name, main(), do not run tests when
      // building it and raise error on file conflicts.
      assemblyJarName in assembly :=
        "renaissance-" + (version in renaissanceCore).value + ".jar",
      mainClass in assembly := Some(classOf[Launcher].getName),
      test in assembly := {},
      assemblyMergeStrategy in assembly := {
        case PathList("META-INF", "MANIFEST.MF") => MergeStrategy.discard
        case x                                   => MergeStrategy.singleOrError
      },
      javaOptions in Compile ++= {
        if (remoteDebug.value) {
          Seq("-agentlib:jdwp=transport=dt_socket,server=y,suspend=y,address=8000")
        } else {
          Seq()
        }
      },
      onLoad in Global := {
        val old = (onLoad in Global).value
        old.andThen(startupTransition)
      }
    )
    .dependsOn(
      renaissanceCore
    )
  allProjects.foldLeft(p)(_ aggregate _)
}

def generateJmhWrapperBenchmarkClass(
  name: String,
  packageName: String,
  outputDir: File
): File = {
  val content = s"""
     package $packageName;

     import java.util.concurrent.TimeUnit;
     import org.openjdk.jmh.annotations.*;
     import org.renaissance.RenaissanceBenchmark;
     import org.renaissance.JmhRenaissanceBenchmark;

     @State(Scope.Benchmark)
     @OutputTimeUnit(TimeUnit.MILLISECONDS)
     public class Jmh_$name extends JmhRenaissanceBenchmark {
       public String benchmarkName() {
           return RenaissanceBenchmark.kebabCase("$name");
       }

       @Setup(Level.Trial)
       public void setUpBeforeAll() {
         defaultSetUpBeforeAll();
       }

       @Setup(Level.Iteration)
       public void setUp() {
         defaultSetUp();
       }

       @TearDown(Level.Iteration)
       public void tearDown() {
         defaultTearDown();
       }

       @TearDown(Level.Trial)
       public void tearDownAfterAll() {
         defaultTearDownAfterAll();
       }

       @Benchmark
       @BenchmarkMode(Mode.AverageTime)
       @OutputTimeUnit(TimeUnit.MILLISECONDS)
       @Measurement(timeUnit = TimeUnit.MILLISECONDS)
       public void run() {
         defaultRun();
       }
     }
   """
  val outputPackageDir =
    new File(outputDir.toString + "/" + packageName.split("\\.").mkString("/"))
  outputPackageDir.mkdirs()
  val outputFile = new File(outputPackageDir, "Jmh_" + name + ".java")
  IO.write(outputFile, content, StandardCharsets.UTF_8)
  outputFile
}

def generateJmhWrapperBenchmarkClasses(
  outputDir: File,
  logger: Logger,
  nonGpl: Boolean,
  groupJars: Seq[(String, Seq[File], Seq[File])]
) = {
  val perProjectBenchmarkClasses = for ((project, allJars, loadedJars) <- groupJars) yield {
    // Scan project jars for benchmarks and fill the property file.
    logger.info(s"Generating JMH wrappers for project $project")
    for {
      info <- listBenchmarks(allJars, None)
      if !nonGpl || info.distro() == License.MIT
    } yield {
      generateJmhWrapperBenchmarkClass(
        info.benchClass.getSimpleName,
        info.benchClass.getPackage.getName,
        outputDir)
    }
  }

  perProjectBenchmarkClasses.flatten
}

lazy val renaissanceJmh = (project in file("renaissance-jmh"))
  .enablePlugins(JmhPlugin)
  .settings(
    name := "renaissance-jmh",
    version := (version in renaissance).value,
    organization := (organization in renaissance).value,
    scalafmtConfig := Some(file(".scalafmt.conf")),
    nonGplOnly := (nonGplOnly in renaissance).value,
    mainClass in assembly := Some("org.openjdk.jmh.Main"),
    sourceGenerators in Compile := Def.taskDyn {
      val log = streams.value.log
      val outputDir = sourceManaged.in(Compile).value
      val nonGpl = nonGplOnly.value
      projectJars.map { groupJars =>
        generateJmhWrapperBenchmarkClasses(outputDir, log, nonGpl, groupJars)
      }
    }.taskValue +: (sourceGenerators in Compile).value,
    assembly in Jmh := ((assembly in Jmh) dependsOn (compile in Jmh)).value,
    assemblyMergeStrategy in assembly := {
      case PathList("scala", xs @ _*) =>
        MergeStrategy.discard
      case x =>
        val oldStrategy = (assemblyMergeStrategy in assembly).value
        oldStrategy(x)
    }
  )
  .dependsOn(
    renaissance
  )

Project.inConfig(Jmh)(baseAssemblySettings)
