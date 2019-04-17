import java.net.URLClassLoader
import java.nio.charset.StandardCharsets
import java.nio.file.Files
import java.nio.file.StandardCopyOption
import java.util.jar.JarFile
import java.util.regex.Pattern
import scala.collection._
import scala.sys.process._

val renaissanceVersion = "0.1"

val renaissanceScalaVersion = "2.12.8"

val benchmarkProjects = for {
  dir <- file("benchmarks").list()
} yield {
  RootProject(uri("benchmarks/" + dir))
}

// Do not assemble fat JARs in subprojects
aggregate in assembly := false

lazy val renaissanceCore = RootProject(uri("renaissance-core"))

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

// Return tuples with (name, distro license, description and default repetitions)
def listBenchmarks(project: String, classpath: Seq[File]): Seq[(String, String, String, Int)] = {
  val urls = classpath.map(_.toURI.toURL)
  val loader = new URLClassLoader(urls.toArray, ClassLoader.getSystemClassLoader.getParent)
  val baseName = "org.renaissance.RenaissanceBenchmark"
  val dummyName = "org.renaissance.core.Dummy"
  val benchBase = loader.loadClass(baseName)
  val result = new mutable.ArrayBuffer[(String, String, String, Int)]
  for (jar <- classpath) {
    val jarFile = new JarFile(jar)
    val enumeration = jarFile.entries()
    while (enumeration.hasMoreElements) {
      val entry = enumeration.nextElement()
      if (entry.getName.startsWith("org/renaissance") && entry.getName.endsWith(".class")) {
        val name = entry.getName
          .substring(0, entry.getName.length - 6)
          .replace("/", ".")
        val clazz = loader.loadClass(name)
        val isEligible =
          benchBase.isAssignableFrom(clazz) && clazz.getName != baseName &&
            (clazz.getName != dummyName || project == "benchmarks/core")
        if (isEligible) {
          val instance = clazz.newInstance
          val distro = clazz.getMethod("distro").invoke(instance).toString
          val description = clazz.getMethod("description").invoke(instance).toString
          val reps = Integer.parseInt(clazz.getMethod("defaultRepetitions").invoke(instance).toString)
          result += new Tuple4(kebabCase(clazz.getSimpleName), distro, description, reps)
        }
      }
    }
  }
  result
}

def jarsAndListGenerator = Def.taskDyn {
  val projectJarTasks = for {
    p <- benchmarkProjects
  } yield
    Def.task {
      val mainJar = (packageBin in (p, Compile)).value
      val coreJar = (packageBin in (renaissanceCore, Runtime)).value
      val depJars = (dependencyClasspath in (p, Compile)).value.map(_.data).filter(_.isFile)
      val allJars = mainJar +: coreJar +: depJars
      val project = p.asInstanceOf[RootProject].build.getPath
      val jarFiles = for (jar <- allJars) yield {
        val dest = (resourceManaged in Compile).value / project / jar.getName
        dest.getParentFile.mkdirs()
        Files.copy(jar.toPath, dest.toPath, StandardCopyOption.REPLACE_EXISTING)
        dest
      }
      (project, jarFiles)
    }

  // Add the built-in benchmarks.
  val coreJarTask = Def.task {
    val coreJar = (packageBin in (renaissanceCore, Runtime)).value
    val coreJarDest =
      (resourceManaged in Compile).value / "benchmarks" / "core" / coreJar.getName
    coreJarDest.getParentFile.mkdirs()
    Files.copy(coreJar.toPath, coreJarDest.toPath, StandardCopyOption.REPLACE_EXISTING)
    ("benchmarks/core", Seq(coreJarDest))
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
    for ((project, jars) <- groupJars) {
      val jarLine = jars
        .map(jar => project + "/" + jar.getName)
        .mkString(",")
      val projectShort = project.stripPrefix("benchmarks/")
      jarListContent.append(projectShort).append("=").append(jarLine).append("\n")
      for ( (name, license, description, repetitions) <- listBenchmarks(project, jars)) {
        if (!nonGpl || license == "MIT") {
          benchGroupContent.append(name).append("=").append(projectShort).append("\n")
          benchDetails.setProperty("benchmark." + name + ".description", description)
          benchDetails.setProperty("benchmark." + name + ".repetitions", repetitions.toString)
        }
      }
    }
    IO.write(jarListFile, jarListContent.toString, StandardCharsets.UTF_8)
    IO.write(benchGroupFile, benchGroupContent.toString, StandardCharsets.UTF_8)
    benchDetails.store(benchDetailsStream, "Benchmark details")
    benchGroupFile +: benchDetailsFile +: jarListFile +: groupJars.flatMap {
      case (_, jars) => jars
    }
  }
}

val renaissanceFormat = taskKey[Unit](
  "Reformat source code with scalafmt."
)

def createRenaissanceFormatTask = Def.taskDyn {
  val formatTasks = for (p <- benchmarkProjects) yield scalafmt in (p, Compile)
  val testFormatTasks = for (p <- benchmarkProjects) yield scalafmt in (p, Test)
  val buildFormatTasks = for (p <- benchmarkProjects) yield scalafmtSbt in (p, Compile)
  flattenTasks(formatTasks ++ testFormatTasks ++ buildFormatTasks)
}

val renaissanceFormatTask = renaissanceFormat := createRenaissanceFormatTask.value

val renaissanceFormatCheck = taskKey[Unit](
  "Check formatting via scalafmt."
)

def createRenaissanceFormatCheckTask = Def.taskDyn {
  val formatTasks = for (p <- benchmarkProjects) yield scalafmtCheck in (p, Compile)
  val testFormatTasks = for (p <- benchmarkProjects) yield scalafmtCheck in (p, Test)
  val buildFormatTasks = for (p <- benchmarkProjects) yield scalafmtSbtCheck in (p, Compile)
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

lazy val renaissance: Project = {
  val p = Project("renaissance", file("."))
    .settings(
      name := "renaissance",
      version := renaissanceVersion,
      organization := "org.renaissance",
      scalaVersion := renaissanceScalaVersion,
      libraryDependencies ++= Seq(
        "commons-io" % "commons-io" % "2.6",
        "com.github.scopt" %% "scopt" % "4.0.0-RC2"
      ),
      resourceGenerators in Compile += jarsAndListGenerator.taskValue,
      renaissanceFormatTask,
      renaissanceFormatCheckTask,
      fork in run := true,
      cancelable in Global := true,
      remoteDebug := false,
      nonGplOnly := false,

      // Configure fat JAR: specify its name, main(), do not run tests when
      // building it and raise error on file conflicts.
      assemblyJarName in assembly := "renaissance-" + renaissanceVersion + ".jar",
      mainClass in assembly := Some("org.renaissance.RenaissanceSuite"),
      test in assembly := {},
      assemblyMergeStrategy in assembly := {
        case PathList("META-INF", "MANIFEST.MF") => MergeStrategy.discard
        case x => MergeStrategy.singleOrError
      },

      javaOptions in Compile ++= {
        if (remoteDebug.value) {
          Seq("-agentlib:jdwp=transport=dt_socket,server=y,suspend=y,address=8000")
        } else {
          Seq()
        }
      }
    )
    .dependsOn(
      renaissanceCore
    )
  benchmarkProjects.foldLeft(p)(_ aggregate _)
}
