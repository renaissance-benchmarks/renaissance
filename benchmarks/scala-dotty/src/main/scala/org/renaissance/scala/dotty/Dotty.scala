package org.renaissance.scala.dotty

import java.io.FileOutputStream
import java.io._
import java.net.URLClassLoader
import java.nio.file.Paths
import java.util.zip.ZipInputStream

import org.apache.commons.io.IOUtils
import org.renaissance.Config
import org.renaissance.License
import org.renaissance.RenaissanceBenchmark
import org.renaissance.Benchmark._

import scala.collection._

@Name("dotty")
@Group("scala-dotty")
@Summary("Runs the Dotty compiler on a set of source code files.")
@Licenses(Array(License.BSD3))
@Repetitions(50)
class Dotty extends RenaissanceBenchmark {

  // TODO: Consolidate benchmark parameters across the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/27

  private val zipPath = "sources.zip"

  private val dottyPath = Paths.get("target", "dotty")

  private val sourceCodePath = dottyPath.resolve("src")

  private val outputPath = dottyPath.resolve("output")

  private val sources: mutable.Buffer[String] = mutable.Buffer[String]()

  private var sourcePaths: mutable.Buffer[String] = null

  private def unzipSources() = {
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

  private def setUpSourcePaths() = {
    sourcePaths = sources.map(f => sourceCodePath.resolve(f).toString)
  }

  override def setUpBeforeAll(c: Config): Unit = {
    outputPath.toFile.mkdirs()
    unzipSources()
    setUpSourcePaths()
  }

  private val DOTTY_ARG_CLASS_PATH = "-classpath"

  private val DOTTY_ARG_CLASS_FILE_DESTINATION = "-d"

  /**
   * Enable implicit conversions in dotty during compilation which
   * allows the compiler to automatically perform implicit type conversions.
   */
  private val DOTTY_ARG_TYPE_CONVERSION = "-language:implicitConversions"

  override def runIteration(c: Config): Unit = {
    val args = Seq[String](
      DOTTY_ARG_CLASS_PATH,
      Thread.currentThread.getContextClassLoader
        .asInstanceOf[URLClassLoader]
        .getURLs
        .mkString(File.pathSeparator),
      DOTTY_ARG_TYPE_CONVERSION,
      DOTTY_ARG_CLASS_FILE_DESTINATION,
      outputPath.toString
    )
    sourcePaths.map(p => args :+ p).foreach(x => dotty.tools.dotc.Main.process(x.toArray))
  }
}
