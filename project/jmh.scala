import sbt.io.IO

import java.io.File
import java.nio.charset.StandardCharsets
import java.nio.file.Path

object RenaissanceJmh {

  def generateJmhWrapperBenchmarkClass(info: BenchmarkInfo, outputBaseDir: Path): File = {
    val packageName = info.benchClass.getPackage.getName
    val jmhClassName = s"Jmh${info.benchClass.getSimpleName}"

    val content = s"""
package $packageName;

import org.openjdk.jmh.annotations.*;
import org.renaissance.jmh.JmhRenaissanceBenchmark;

import static java.util.concurrent.TimeUnit.MILLISECONDS;

@State(Scope.Benchmark)
@OutputTimeUnit(MILLISECONDS)
@Warmup(iterations = ${info.repetitions})
@Measurement(iterations = ${info.repetitions / 4 + 1})
public class $jmhClassName extends JmhRenaissanceBenchmark {
  public $jmhClassName() { super("${info.name}"); }
}
"""

    val packagePath = packageName.split("[.]").mkString(File.separator)
    val outputDir = outputBaseDir.resolve(packagePath)

    // Use the SBT variant that contains some workarounds for Windows.
    IO.createDirectory(outputDir.toFile)

    val outputFile = outputDir.resolve(jmhClassName + ".java").toFile
    IO.write(outputFile, content, StandardCharsets.UTF_8)
    outputFile
  }

}
