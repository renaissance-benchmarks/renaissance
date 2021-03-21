import org.renaissance.License
import sbt.RootProject
import sbt.io.IO
import sbt.util.Logger

import java.io.File
import java.nio.charset.StandardCharsets

object RenaissanceJmh {

  def generateJmhWrapperBenchmarkClass(info: BenchmarkInfo, outputDir: File): File = {
    val packageName = info.benchClass.getPackage.getName
    val jmhClassName = "Jmh" + info.benchClass.getSimpleName

    val content = s"""
package ${packageName};

import org.openjdk.jmh.annotations.*;
import org.renaissance.jmh.JmhRenaissanceBenchmark;

import static java.util.concurrent.TimeUnit.MILLISECONDS;

@State(Scope.Benchmark)
@OutputTimeUnit(MILLISECONDS)
@Warmup(iterations = ${info.repetitions})
@Measurement(iterations = ${info.repetitions / 4 + 1})
public class ${jmhClassName} extends JmhRenaissanceBenchmark {
  public ${jmhClassName}() { super("${info.name}"); }
}
"""

    val outputPackageDir =
      new File(outputDir.toString + "/" + packageName.split("\\.").mkString("/"))
    outputPackageDir.mkdirs()
    val outputFile = new File(outputPackageDir, jmhClassName + ".java")
    IO.write(outputFile, content, StandardCharsets.UTF_8)
    outputFile
  }

  def generateJmhWrapperBenchmarkClasses(
    outputDir: File,
    logger: Logger,
    nonGpl: Boolean,
    groupJars: Seq[(String, String, Seq[File], Seq[File])]
  ) = {
    val perProjectBenchmarkClasses = for {
      (projectName, projectPath, allJars, _) <- groupJars
      // TODO: Filter projects in the build file if possible
      if projectPath.startsWith("benchmarks/")
    } yield {
      // Scan project jars for benchmarks and fill the property file.
      logger.info(s"Generating JMH wrappers for project $projectPath")
      for {
        info <- Benchmarks.listBenchmarks(projectName, allJars, None)
        // TODO: Filter projects in the build file if possible
        if (!nonGpl || info.distro() == License.MIT) &&
          (!info.groups.contains("dummy") || info.name == "dummy-empty")
      } yield {
        generateJmhWrapperBenchmarkClass(info, outputDir)
      }
    }

    perProjectBenchmarkClasses.flatten
  }
}
