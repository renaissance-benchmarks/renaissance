package org.renaissance.eclipse

import java.io.{File, PrintWriter, StringWriter}
import java.io.FileOutputStream
import java.net.URLClassLoader
import java.nio.file.Paths
import java.util.zip.ZipInputStream

import org.eclipse.jdt.core.compiler.batch.BatchCompiler
import org.renaissance.Benchmark
import org.renaissance.Benchmark._
import org.renaissance.BenchmarkContext
import org.renaissance.BenchmarkResult
import org.renaissance.BenchmarkResult.Validators
import org.renaissance.License

import scala.collection._

@Name("ecj")
@Group("eclipse")
@Summary("Runs the Eclipse JDT compiler on a set of source code files.")
@Licenses(Array(License.EPL1))
@Repetitions(60)
@Configurations(Array(new Configuration(name = "test"), new Configuration(name = "jmh")))
final class JdtCompiler extends Benchmark {

  // TODO: Consolidate benchmark parameters across the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/27

  private val recompilationCount = 5

  private val zipPath = "algorithms.zip"

  private val ecjPath = Paths.get("target", "ecj")

  private val sourceCodePath = ecjPath.resolve("src")

  private val outputPath = ecjPath.resolve("output")

  private val sources: mutable.Buffer[String] = mutable.Buffer[String]()

  private var sourcePaths: mutable.Buffer[String] = _

  private def unzipSources(): Unit = {
    val zis = new ZipInputStream(this.getClass.getResourceAsStream("/" + zipPath))
    val destination = sourceCodePath

    Stream.continually(zis.getNextEntry).takeWhile(_ != null).foreach { file =>
      if (!file.isDirectory) {
        val outPath = destination.resolve(file.getName)
        val outPathParent = outPath.getParent
        if (!outPathParent.toFile.exists()) {
          outPathParent.toFile.mkdirs()
        }

        val outFile = outPath.toFile
        val out = new FileOutputStream(outFile)
        val buffer = new Array[Byte](4096)
        Stream.continually(zis.read(buffer)).takeWhile(_ != -1).foreach(out.write(buffer, 0, _))
        out.close()
        sources += file.getName
      }
    }
  }

  private def setUpSourcePaths(): Unit = {
    sourcePaths = sources.map(f => sourceCodePath.resolve(f).toString)
  }

  override def setUpBeforeAll(c: BenchmarkContext): Unit = {
    outputPath.toFile.mkdirs()
    unzipSources()
    setUpSourcePaths()
  }

  private val ECJ_ARG_WARN = "-warn:none"

  private val ECJ_ARG_REPEAT = "-repeat"

  private val ECJ_ARG_TARGET = "-target"

  private val ECJ_ARG_TARGET_VERSION = "1.8"

  private val ECJ_ARG_COMPLIANCE_LEVEL = "-1.8"

  private val ECJ_ARG_CLASS_PATH = "-classpath"

  private val ECJ_ARG_CLASS_FILE_DESTINATION = "-d"

  override def run(c: BenchmarkContext): BenchmarkResult = {
    /*
     * The same trick that is being used for the Dotty benchmark is required here.
     * For context, see https://github.com/renaissance-benchmarks/renaissance/issues/176.
     */
    val generatedClasspath = Thread.currentThread.getContextClassLoader
      .asInstanceOf[URLClassLoader]
      .getURLs
      .map(url => new java.io.File(url.toURI).getPath)
      .mkString(File.pathSeparator)
    val args = Seq[String](
      ECJ_ARG_WARN,
      ECJ_ARG_REPEAT,
      recompilationCount.toString,
      ECJ_ARG_TARGET,
      ECJ_ARG_TARGET_VERSION,
      ECJ_ARG_COMPLIANCE_LEVEL,
      ECJ_ARG_CLASS_PATH,
      generatedClasspath,
      ECJ_ARG_CLASS_FILE_DESTINATION,
      outputPath.toString
    )
    val stdout = new StringWriter
    val stderr = new StringWriter
    val success = BatchCompiler.compile(
      args.toArray ++ sourcePaths.filter(f => f.endsWith(".java")),
      new PrintWriter(stdout),
      new PrintWriter(stderr),
      null
    )

    Validators.dummy()
  }
}
