import java.lang.annotation.Annotation
import java.util.regex.Pattern

import org.renaissance.Benchmark
import org.renaissance.Benchmark._
import org.renaissance.License
import org.renaissance.RenaissanceBenchmark

class BenchmarkInfo(val benchClass: Class[_ <: RenaissanceBenchmark]) {

  private def kebabCase(s: String): String = {
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
    )
  }
}
