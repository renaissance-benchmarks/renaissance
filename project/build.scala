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

class BenchmarkInfo(val benchClass: Class[_ <: Benchmark]) {

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

  private def getAnnotation[T <: Annotation](annotationClass: Class[T]) = {
    benchClass.getDeclaredAnnotation(annotationClass)
  }

  def className = benchClass.getName

  def name(): String = {
    val annotation = getAnnotation(classOf[Name])
    if (annotation != null) {
      annotation.value()
    } else {
      kebabCase(benchClass.getSimpleName)
    }
  }

  def group(): String = {
    val annotation = getAnnotation(classOf[Group])
    if (annotation != null) {
      annotation.value()
    } else {
      val groupPkg = getPackageRelativeTo(benchClass, classOf[Benchmark])
      groupPkg.replaceAll("[.]", "-")
    }
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

  def summary(): String = {
    val annotation = getAnnotation(classOf[Summary])
    if (annotation != null) annotation.value() else ""
  }

  def description(): String = {
    val annotation = getAnnotation(classOf[Description])
    if (annotation != null) annotation.value() else ""
  }

  def repetitions(): Int = {
    val annotation = getAnnotation(classOf[Repetitions])
    if (annotation != null) annotation.value() else 20
  }

  def parameters(): Map[String, String] = {
    val result = new mutable.HashMap[String, String]

    val configs = getAnnotation(classOf[Configurations])
    if (configs != null) {
      val params = getAnnotation(classOf[Parameters])

      for (config <- configs.value) {
        val confBase = s"parameters.${config.name}";

        // Set default parameter values first
        if (params != null) {
          for (param <- params.value) {
            val keyBase = s"${confBase}.${param.name}"
            result.put(s"${keyBase}.value", param.defaultValue)
            result.put(s"${keyBase}.summary", param.summary)
          }
        }

        // Override with configuration-specific values, but only
        // allow to update existing keys. This ensures that only
        // known keys will be overridden.
        for (setting <- config.settings) {
          val elements = setting.split("=").map(x => x.trim)
          assert(elements.length == 2)

          val (name, value) = (elements(0), elements(1))
          val key = s"${confBase}.${name}.value"
          if (!result.contains(key)) {
            throw new AssertionError(s"undefined parameter: ${name}")
          }

          result.put(key, value)
        }
      }
    }

    result.toMap
  }

  def licenses(): Array[License] = {
    val annotation = getAnnotation(classOf[Licenses])
    if (annotation != null) annotation.value() else Array()
  }

  def printableLicenses(): String = {
    licenses.map(l => l.toString).mkString(",")
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
      "class" -> className,
      "name" -> name,
      "group" -> group,
      "summary" -> summary,
      "description" -> description,
      "licenses" -> printableLicenses,
      "repetitions" -> repetitions.toString,
      "distro" -> distro.toString
    ) ++ parameters
  }

}

object Benchmarks {

  // Return tuples with (name, distro license, all licenses, description and default repetitions)
  def listBenchmarks(classpath: Seq[File], logger: Option[Logger]): Seq[BenchmarkInfo] = {
    //
    // Load the benchmark base class and create a class loader for the project
    // with the class loader of the base class as its parent. This will allow
    // us to use core classes here.
    //
    val benchBase = classOf[Benchmark]
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

  def logBenchmark(b: BenchmarkInfo, logger: Logger) = {
    logger.info(s"class: ${b.className}")
    logger.info(s"\tbenchmark: ${b.group}/${b.name}")
    logger.info(s"\tlicensing: ${b.printableLicenses} => ${b.distro}")
    logger.info(s"\trepetitions: ${b.repetitions}")
    logger.info(s"\tsummary: ${b.summary}")
  }
}
