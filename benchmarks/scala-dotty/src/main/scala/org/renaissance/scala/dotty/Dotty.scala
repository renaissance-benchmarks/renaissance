package org.renaissance.scala.dotty

import java.io._
import java.net.URLClassLoader
import java.nio.file.Paths
import java.util.zip.ZipInputStream

import org.apache.commons.io.IOUtils
import org.renaissance.Benchmark
import org.renaissance.Benchmark._
import org.renaissance.BenchmarkContext
import org.renaissance.BenchmarkResult
import org.renaissance.BenchmarkResult.Validators
import org.renaissance.License

import scala.collection._

@Name("dotty")
@Group("scala-dotty")
@Summary("Runs the Dotty compiler on a set of source code files.")
@Licenses(Array(License.BSD3))
@Repetitions(50)
// Work around @Repeatable annotations not working in this Scala version.
@Configurations(Array(new Configuration(name = "test"), new Configuration(name = "jmh")))
final class Dotty extends Benchmark {

  // TODO: Consolidate benchmark parameters across the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/27

  private val zipPath = "sources.zip"

  private val dottyPath = Paths.get("target", "dotty")

  private val sourceCodePath = dottyPath.resolve("src")

  private val outputPath = dottyPath.resolve("output")

  private val sources: mutable.Buffer[String] = mutable.Buffer[String]()

  private var sourcePaths: mutable.Buffer[String] = _

  private def unzipSources(): Unit = {
    val zis = new ZipInputStream(this.getClass.getResourceAsStream("/" + zipPath))
    val target = sourceCodePath.toFile
    var nextEntry = zis.getNextEntry
    while (nextEntry != null) {
      val name = nextEntry.getName
      val f = new File(target, name)
      if (!f.isDirectory) {
        // Create directories.
        val parent = f.getParentFile
        if (parent != null) parent.mkdirs
        val targetStream = new FileOutputStream(f)
        IOUtils.copy(zis, targetStream)
        targetStream.close()
        sources += name
        nextEntry = zis.getNextEntry
      }
    }
    zis.close()
  }

  private def setUpSourcePaths(): Unit = {
    sourcePaths = sources.map(f => sourceCodePath.resolve(f).toString)
  }

  override def setUpBeforeAll(c: BenchmarkContext): Unit = {
    outputPath.toFile.mkdirs()
    unzipSources()
    setUpSourcePaths()
  }

  private val DOTTY_ARG_CLASS_PATH = "-classpath"

  private val DOTTY_ARG_CLASS_FILE_DESTINATION = "-d"

  /**
   * Allows the compiler to automatically perform implicit type conversions.
   */
  private val DOTTY_ARG_TYPE_CONVERSION = "-language:implicitConversions"

  override def run(c: BenchmarkContext): BenchmarkResult = {
    /*
     * Construct the classpath for the compiler. Unfortunately, Dotty is
     * unable to use current classloader (either of this class or this
     * thread) and thus we have to explicitly pass it. Note that
     * -usejavacp would not work here as that reads from java.class.path
     * property and we do not want to modify global properties here.
     *
     * Therefore, we leverage the fact that we know that our classloader
     * is actually a URLClassLoader that loads the benchmark JARs
     * from temporary directory. And we convert all the URLs to
     * plain file paths.
     *
     * Note that using URLs as-is is not possible as that prepends the
     * "file:/" protocol that is not handled well on Windows when
     * on classpath.
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

    val args = Seq[String](
      DOTTY_ARG_CLASS_PATH,
      classPath,
      DOTTY_ARG_TYPE_CONVERSION,
      DOTTY_ARG_CLASS_FILE_DESTINATION,
      outputPath.toString
    )

    // Call dotc.Main through a Java bridge method.
    sourcePaths.map(p => args :+ p).foreach(x => JavaDotty.process(x.toArray))

    // TODO: add proper validation
    Validators.dummy()
  }
}
