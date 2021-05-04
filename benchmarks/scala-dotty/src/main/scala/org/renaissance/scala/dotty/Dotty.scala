package org.renaissance.scala.dotty

import org.renaissance.Benchmark
import org.renaissance.Benchmark._
import org.renaissance.BenchmarkContext
import org.renaissance.BenchmarkResult
import org.renaissance.BenchmarkResult.Validators
import org.renaissance.License

import java.io._
import java.net.URLClassLoader
import java.nio.file.Files.copy
import java.nio.file.Files.createDirectories
import java.nio.file.Files.notExists
import java.nio.file.Path
import java.nio.file.StandardCopyOption.REPLACE_EXISTING
import java.util.zip.ZipInputStream
import scala.collection._

// Keep to allow cross-compilation with Scala 2.11 and 2.12.
import scala.collection.compat._

@Name("dotty")
@Group("scala-dotty")
@Summary("Runs the Dotty compiler on a set of source code files.")
@Licenses(Array(License.BSD3))
@Repetitions(50)
@Parameter(
  name = "batch_compilation",
  defaultValue = "false",
  summary = "Compiles all source files in batch mode instead of one by one."
)
@Configuration(name = "test")
@Configuration(name = "jmh")
final class Dotty extends Benchmark {

  // TODO: Consolidate benchmark parameters across the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/27

  private val sourcesInputResource = "/sources.zip"

  private var dottyBaseArgs: Seq[String] = _

  private var dottyInvocations: Seq[Array[String]] = _

  private def unzipResource(resourceName: String, outputDir: Path) = {
    val zis = new ZipInputStream(this.getClass.getResourceAsStream(resourceName))

    try {
      val sources = mutable.Buffer[Path]()
      LazyList.continually(zis.getNextEntry).takeWhile(_ != null).foreach { zipEntry =>
        if (!zipEntry.isDirectory) {
          val target = outputDir.resolve(zipEntry.getName)
          val parent = target.getParent
          if (parent != null && notExists(parent)) {
            createDirectories(parent)
          }

          copy(zis, target, REPLACE_EXISTING)
          sources += target
        }
      }

      sources.toSeq
    } finally {
      zis.close()
    }
  }

  override def setUpBeforeAll(bc: BenchmarkContext): Unit = {
    /*
     * Construct the classpath for the compiler. Unfortunately, Dotty is
     * unable to use the current classloader (either of this class or this
     * thread), so we have to pass the classpath to it explicitly. Note
     * that -usejavacp would not work as that reads from java.class.path
     * property and we do not want to modify global properties here.
     *
     * Because we know that our classloader is actually an URLClassLoader
     * which loads the benchmark JARs from a temporary directory, we just
     * convert all the URLs to plain file paths.
     *
     * Note that using the URLs directly is not possible, because they
     * contain the "file://" protocol prefix, which is not handled well
     * on Windows (when on the classpath).
     *
     * Note that it would be best to pass the classloader to the compiler
     * but that seems to be impossible with current API (see discussion
     * at https://github.com/renaissance-benchmarks/renaissance/issues/176).
     */
    val classPath = Thread.currentThread.getContextClassLoader
      .asInstanceOf[URLClassLoader]
      .getURLs
      .map(url => new java.io.File(url.toURI).getPath)
      .mkString(File.pathSeparator)

    val scratchDir = bc.scratchDirectory()
    val outputDir = createDirectories(scratchDir.resolve("output"))

    dottyBaseArgs = Seq[String](
      "-classpath",
      classPath,
      // Allow the compiler to automatically perform implicit type conversions.
      "-language:implicitConversions",
      // Output directory for compiled classes.
      "-d",
      outputDir.toString
    )

    val sourceDir = scratchDir.resolve("src")
    val sourceFiles = unzipResource(sourcesInputResource, sourceDir)

    val batchCompilation = bc.parameter("batch_compilation").toBoolean
    if (batchCompilation) {
      // Compile all sources as a batch.
      val dottyArgs = (dottyBaseArgs ++ sourceFiles.map(_.toString)).toArray
      dottyInvocations = Seq(dottyArgs)
    } else {
      // Compile sources one-by-one.
      dottyInvocations = sourceFiles.map(p => (dottyBaseArgs :+ p.toString).toArray)
    }
  }

  override def run(c: BenchmarkContext): BenchmarkResult = {
    dottyInvocations.foreach { dottyArgs =>
      dotty.tools.dotc.Main.process(dottyArgs)
    }

    // TODO: add proper validation
    Validators.dummy()
  }
}
