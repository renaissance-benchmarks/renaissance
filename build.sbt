import java.net.URLClassLoader
import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path, StandardCopyOption}
import java.util.jar.JarFile
import java.util.regex.Pattern
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

def kebabCase(s: String): String = {
  // This functionality is duplicated in the RenaissanceBenchmark class.
  val camelCaseName = if (s.last == '$') s.init else s
  val pattern = Pattern.compile("([A-Za-z])([A-Z])")
  var result = camelCaseName
  do {
    val last = result
    result = pattern.matcher(result).replaceFirst("$1-$2")
    if (last == result) {
      return result.toLowerCase()
    }
  } while (true)
  sys.error("unreachable")
}

// Return tuples with (name, distro license, all licenses, description and default repetitions)
def listBenchmarks(
  project: String,
  classpath: Seq[File]
): Seq[(String, String, String, String, Int)] = {
  val urls = classpath.map(_.toURI.toURL)
  val loader = new URLClassLoader(urls.toArray, ClassLoader.getSystemClassLoader.getParent)
  val benchBase = loader.loadClass("org.renaissance.RenaissanceBenchmark")
  val excludePattern = Pattern.compile("org[.]renaissance(|[.]harness|[.]util)")
  val result = new mutable.ArrayBuffer[(String, String, String, String, Int)]
  for (jar <- classpath) {
    val jarFile = new JarFile(jar)
    val enumeration = jarFile.entries()
    while (enumeration.hasMoreElements) {
      val entry = enumeration.nextElement()
      if (entry.getName.startsWith("org/renaissance") && entry.getName.endsWith(".class")) {
        val name = entry.getName
          .substring(0, entry.getName.length - ".class".length)
          .replace("/", ".")
        val clazz = loader.loadClass(name)

        val isEligible =
          !excludePattern.matcher(clazz.getPackage.getName).matches() &&
            benchBase.isAssignableFrom(clazz)
        if (isEligible) {
          // Can we PLEASE have a reasonable logging support in SBT?
          // And NOT the streams.value or sLog.value that cannot be used here?
          // It's a turing-complete build system and we can't even log conveniently!
          println("eligible benchmark: " + clazz.getName)

          val instance = clazz.getDeclaredConstructor().newInstance()
          val distro = clazz.getMethod("distro").invoke(instance).toString
          val licenses = clazz
            .getMethod("licenses")
            .invoke(instance)
            .asInstanceOf[Array[Object]]
            .map(x => x.toString)
            .mkString(",")
          val description = clazz.getMethod("description").invoke(instance).toString
          val reps =
            Integer.parseInt(clazz.getMethod("defaultRepetitions").invoke(instance).toString)
          result += ((kebabCase(clazz.getSimpleName), distro, licenses, description, reps))
        }
      }
    }
  }
  result
}

def jarsAndListGenerator = Def.taskDyn {
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

  // Add the built-in benchmarks.
  val coreJarTask = Def.task {
    val coreJar = (packageBin in (renaissanceCore, Runtime)).value
    val coreJarDest =
      (resourceManaged in Compile).value / "benchmarks" / "core" / coreJar.getName
    coreJarDest.getParentFile.mkdirs()
    Files.copy(coreJar.toPath, coreJarDest.toPath, StandardCopyOption.REPLACE_EXISTING)
    ("benchmarks/core", Seq(coreJarDest), Seq(coreJarDest))
  }
  val jarTasks = coreJarTask +: projectJarTasks
  val nonGpl = nonGplOnly.value

  // Flatten list, create a groups-jars file, and a benchmark-group file.
  flattenTasks(jarTasks).map { groupJars =>
    val jarListFile = (resourceManaged in Compile).value / "groups-jars.txt"
    val jarListContent = new StringBuilder
    val benchGroupFile = (resourceManaged in Compile).value / "benchmark-group.txt"
    val benchGroupContent = new StringBuilder
    val benchDetailsFile = (resourceManaged in Compile).value / "benchmark-details.properties"
    val benchDetailsStream = new java.io.FileOutputStream(benchDetailsFile)
    val benchDetails = new java.util.Properties

    // Add the benchmarks from the different project groups.
    for ((project, allJars, loadedJars) <- groupJars) {
      val jarLine = loadedJars
        .map(jar => project + "/" + jar.getName)
        .mkString(",")
      val projectShort = project.stripPrefix("benchmarks/")
      jarListContent.append(projectShort).append("=").append(jarLine).append("\n")
      for ((name, distroLicense, licenses, description, repetitions) <- listBenchmarks(
             project,
             allJars
           )) {
        if (!nonGpl || distroLicense == "MIT") {
          benchGroupContent.append(name).append("=").append(projectShort).append("\n")
          benchDetails.setProperty("benchmark." + name + ".description", description)
          benchDetails.setProperty("benchmark." + name + ".repetitions", repetitions.toString)
          benchDetails.setProperty("benchmark." + name + ".distro", distroLicense.toString)
          benchDetails.setProperty("benchmark." + name + ".licenses", licenses.toString)
        }
      }
    }
    IO.write(jarListFile, jarListContent.toString, StandardCharsets.UTF_8)
    IO.write(benchGroupFile, benchGroupContent.toString, StandardCharsets.UTF_8)
    benchDetails.store(benchDetailsStream, "Benchmark details")
    benchGroupFile +: benchDetailsFile +: jarListFile +: groupJars.flatMap {
      case (_, jars, _) => jars
    }
  }
}

// TODO These tasks may be unnecessary, aggregation seems to work
val renaissanceFormat = taskKey[Unit](
  "Reformat source code with scalafmt."
)

def createRenaissanceFormatTask = Def.taskDyn {
  val formatTasks = for (p <- subProjects) yield scalafmt in (p, Compile)
  val testFormatTasks = for (p <- subProjects) yield scalafmt in (p, Test)
  val buildFormatTasks = for (p <- allProjects) yield scalafmtSbt in (p, Compile)
  flattenTasks(formatTasks ++ testFormatTasks ++ buildFormatTasks)
}

val renaissanceFormatTask = renaissanceFormat := createRenaissanceFormatTask.value

val renaissanceFormatCheck = taskKey[Unit](
  "Check formatting via scalafmt."
)

def createRenaissanceFormatCheckTask = Def.taskDyn {
  val formatTasks = for (p <- subProjects) yield scalafmtCheck in (p, Compile)
  val testFormatTasks = for (p <- subProjects) yield scalafmtCheck in (p, Test)
  val buildFormatTasks = for (p <- allProjects) yield scalafmtSbtCheck in (p, Compile)
  flattenTasks(formatTasks ++ testFormatTasks ++ buildFormatTasks)
}

val renaissanceFormatCheckTask = renaissanceFormatCheck := createRenaissanceFormatCheckTask.value

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
      renaissanceFormatTask,
      renaissanceFormatCheckTask,
      fork in run := true,
      cancelable in Global := true,
      remoteDebug := false,
      nonGplOnly := false,
      setupPrePush := addLink(file("tools") / "pre-push", file(".git") / "hooks" / "pre-push"),
      packageOptions := Seq(
        sbt.Package.ManifestAttributes(
          ("Renaissance-Version", (version in renaissanceCore).value)
        )
      ),
      // Configure fat JAR: specify its name, main(), do not run tests when
      // building it and raise error on file conflicts.
      assemblyJarName in assembly := "renaissance-" + (version in renaissanceCore).value + ".jar",
      mainClass in assembly := Some("org.renaissance.Launcher"),
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
