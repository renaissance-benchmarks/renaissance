import java.io.File
import java.lang.annotation.Annotation
import java.net.URLClassLoader
import java.util.jar.JarFile
import java.util.regex.Pattern

import org.renaissance.Benchmark
import org.renaissance.Benchmark._
import org.renaissance.License
import sbt.util.Logger

import scala.collection._

class BenchmarkInfo(val module: String, val benchClass: Class[_ <: Benchmark]) {

  private def kebabCase(s: String): String = {
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

  private def getAnnotation[A <: Annotation](annotationClass: Class[A]) = {
    Option(benchClass.getDeclaredAnnotation(annotationClass))
  }

  private def getAnnotations[A <: Annotation](annotationClass: Class[A]) = {
    benchClass.getDeclaredAnnotationsByType(annotationClass)
  }

  def className: String = benchClass.getName

  def name(): String = {
    getAnnotation(classOf[Name]).map(_.value()).getOrElse(kebabCase(benchClass.getSimpleName))
  }

  def groups(): Seq[String] = {
    val gs = getAnnotations(classOf[Group])
    if (gs.isEmpty) Seq(getDefaultGroup()) else gs.map(_.value)
  }

  private def getDefaultGroup(): String = {
    val groupPkg = getPackageRelativeTo(benchClass, classOf[Benchmark])
    groupPkg.replaceAll("[.]", "-")
  }

  private def getPackageRelativeTo(target: Class[_], base: Class[_]): String = {
    val targetPkg = target.getPackage.getName
    val basePkg = base.getPackage.getName
    if (targetPkg.startsWith(basePkg)) {
      targetPkg.substring(basePkg.length() + 1)
    } else {
      targetPkg
    }
  }

  def printableGroups(): String = {
    groups().mkString(",")
  }

  def summary(): String = {
    getAnnotation(classOf[Summary]).map(_.value()).getOrElse("")
  }

  def description: String = {
    getAnnotation(classOf[Description]).map(_.value()).getOrElse("")
  }

  def repetitions: Int = {
    getAnnotation(classOf[Repetitions]).map(_.value()).getOrElse(20)
  }

  def parameters(): Map[String, String] = {
    getAnnotations(classOf[Parameter])
      .flatMap(p =>
        Array(
          s"parameter.${p.name}.default" -> p.defaultValue,
          s"parameter.${p.name}.summary" -> p.summary
        )
      )
      .toMap
  }

  private def parameterDefaults(confName: String) = {
    getAnnotations(classOf[Parameter])
      .map(p => s"configuration.${confName}.${p.name}" -> p.defaultValue())
      .toMap
  }

  def configurations(): Map[String, String] = {
    //
    // Create default configuration and initialize each configuration
    // using the default values parameters. Then apply configuration-specific
    // settings that override the defaults, but only for known parameters.
    //
    val result = mutable.Map[String, String]()
    result ++= parameterDefaults("default")

    for (conf <- getAnnotations(classOf[Configuration])) {
      result ++= parameterDefaults(conf.name())

      for (setting <- conf.settings) {
        val elements = setting.split("=").map(x => x.trim)
        if (elements.length != 2) {
          throw new IllegalArgumentException(
            s"malformed setting in configuration '${conf.name}': ${setting}"
          )
        }

        val (name, value) = (elements(0), elements(1))
        val paramKey = s"configuration.${conf.name}.${name}"
        if (!result.contains(paramKey)) {
          throw new NoSuchElementException(
            s"unknown parameter in configuration '${conf.name}': ${name}"
          )
        }

        result.put(paramKey, value)
      }
    }

    result.toMap
  }

  def jvmVersionMin(): String = {
    // Require at least JVM 1.8 where unspecified.
    getAnnotation(classOf[RequiresJvm]).map(_.value()).getOrElse("1.8")
  }

  def jvmVersionMax(): String = {
    getAnnotation(classOf[SupportsJvm]).map(_.value()).getOrElse("")
  }

  def licenses(): Array[License] = {
    getAnnotation(classOf[Licenses]).map(_.value()).getOrElse(Array())
  }

  def printableLicenses(): String = {
    licenses.map(_.toString).mkString(",")
  }

  // Determine target Renaissance distro based on the licenses
  private def distroFromLicenses(licenses: Array[License]): License = {
    for (license <- licenses) {
      license match {
        case License.GPL2 | License.GPL3 | License.EPL1 | License.MPL2 =>
          return License.GPL3
        case _ =>
        // MIT-compatible, check next entry
      }
    }

    License.MIT
  }

  def distro(): License = distroFromLicenses(licenses())

  def toMap(): Map[String, String] = {
    Map(
      "module" -> module,
      "class" -> className,
      "name" -> name,
      "groups" -> printableGroups,
      "summary" -> summary,
      "description" -> description,
      "licenses" -> printableLicenses,
      "repetitions" -> repetitions.toString,
      "distro" -> distro().toString,
      "jvm_version_min" -> jvmVersionMin(),
      "jvm_version_max" -> jvmVersionMax()
    ) ++ parameters ++ configurations()
  }

}

object Benchmarks {

  // Return tuples with (name, distro license, all licenses, description and default repetitions)
  def listBenchmarks(
    projectName: String,
    classPath: Seq[File],
    logger: Option[Logger]
  ): Seq[BenchmarkInfo] = {
    //
    // Load the benchmark base class and create a class loader for the project
    // with the class loader of the base class as its parent. This will allow
    // us to use core classes here.
    //
    val benchBase = classOf[Benchmark]
    val urls = classPath.map(_.toURI.toURL).toArray
    val loader = new URLClassLoader(urls, benchBase.getClassLoader)
    val excludePattern = Pattern.compile("org[.]renaissance(|[.]harness|[.]core)")

    //
    // Scan all JAR files for classes in the org.renaissance package implementing
    // the benchmark interface and collect metadata from class annotations.
    //
    val result = new mutable.ArrayBuffer[BenchmarkInfo]
    for (jarFile <- classPath.map(jar => new JarFile(jar))) {
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
            val info = new BenchmarkInfo(projectName, benchClass)
            if (logger.nonEmpty) logBenchmark(info, logger.get)
            result += info
          }
        }
      }
    }

    result
  }

  def logBenchmark(b: BenchmarkInfo, logger: Logger) = {
    logger.info(s"class: ${b.className}")
    logger.info(s"\tbenchmark: ${b.name} (${b.printableGroups})")
    logger.info(s"\tlicensing: ${b.printableLicenses} => ${b.distro}")
    logger.info(s"\trepetitions: ${b.repetitions}")
    logger.info(s"\tsummary: ${b.summary}")
  }
}
