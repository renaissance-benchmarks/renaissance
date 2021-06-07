package org.renaissance.scala.dotty

import dotty.tools.dotc.interfaces.AbstractFile
import dotty.tools.dotc.interfaces.CompilerCallback
import dotty.tools.dotc.interfaces.Diagnostic
import dotty.tools.dotc.interfaces.SimpleReporter
import dotty.tools.dotc.interfaces.SourceFile
import dotty.tools.dotc.{Main => DottyMain}
import org.renaissance.Benchmark
import org.renaissance.Benchmark._
import org.renaissance.BenchmarkContext
import org.renaissance.BenchmarkResult
import org.renaissance.BenchmarkResult.Assert
import org.renaissance.BenchmarkResult.ValidationException
import org.renaissance.License
import org.renaissance.core.DirUtils

import java.io._
import java.net.URLClassLoader
import java.nio.file.Files.copy
import java.nio.file.Files.createDirectories
import java.nio.file.Files.notExists
import java.nio.file.Path
import java.nio.file.Paths
import java.nio.file.StandardCopyOption.REPLACE_EXISTING
import java.security.DigestInputStream
import java.security.MessageDigest
import java.util.zip.ZipInputStream
import scala.collection._
import scala.io.Source

@Name("dotty")
@Group("scala-dotty")
@Summary("Runs the Dotty compiler on a set of source code files.")
@Licenses(Array(License.BSD3))
@Repetitions(50)
@Parameter(
  name = "expected_classes_hash",
  defaultValue = "81e2306d4b9ea9f3fbc8a8851be84e57"
)
@Configuration(name = "test")
@Configuration(name = "jmh")
final class Dotty extends Benchmark {

  // TODO: Consolidate benchmark parameters across the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/27

  private var expectedClassesHash: String = _

  private val sourcesInputResource = "/sources.zip"


  private var dottyArgs: Array[String] = _

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
    val classPathJars = Thread.currentThread.getContextClassLoader
      .asInstanceOf[URLClassLoader]
      .getURLs
      .map(url => new java.io.File(url.toURI).getPath)
      .toBuffer

    val scratchDir = bc.scratchDirectory()
    val outputDir = createDirectories(scratchDir.resolve("out"))


    val sourceDir = scratchDir.resolve("src")
    val sourceFiles = unzipResource(sourcesInputResource, sourceDir)

    val dottyBaseArgs = Seq[String](
      // Mark the sources as transitional.
      "-source",
      "3.0-migration",
      // Class path with dependency jars.
      "-classpath",
      classPathJars.mkString(File.pathSeparator),
      // Output directory for compiled classes.
      "-d",
      outputDir.toString,
      // Set the root of the sources directory. Makes .class files stable.
      "-sourceroot",
      sourceDir.toString
    )

    // Compile all sources as a batch.
    dottyArgs = (dottyBaseArgs ++ sourceFiles.map(_.toString)).toArray

    expectedClassesHash = bc.parameter("expected_classes_hash").value()
  }

  override def run(bc: BenchmarkContext): BenchmarkResult = {
    val result = new CompilationResult
    DottyMain.process(dottyArgs, result, result)

    //
    // TODO: Check if Dotty can be convinced to generate identical .class files
    //
    // Currently, using the -sourceroot option helps stability between runs, but
    // there are slight changes in some of the class files between Renaissance
    // builds, which breaks hash-based validation.
    //
    () => {
      result.errors.foreach(d => {
        val pos = d.position().map(p => s"${p.source()}:${p.line()}: ").orElse("")
        println(s"dotty-error: ${pos}${d.message()}")
      })

      Assert.assertEquals(0, result.errors.length, "compilation errors")
      println(s"digest of generated classes: ${result.digest()}")
      // Assert.assertEquals(expectedClassesHash, result.digest(), "digest of generated classes")
    }
  }

  private class CompilationResult extends SimpleReporter with CompilerCallback {
    val errors = mutable.Buffer[Diagnostic]()
    val warnings = mutable.Buffer[Diagnostic]()

    override def report(diag: Diagnostic): Unit = {
      diag.level() match {
        case Diagnostic.ERROR => errors += diag
        case Diagnostic.WARNING => warnings += diag
        case other => /* ignore */
      }
    }

    val compiledSources = mutable.Buffer[SourceFile]()
    val generatedClasses = mutable.Buffer[AbstractFile]()

    override def onClassGenerated(
      source: SourceFile,
      generatedClass: AbstractFile,
      className: String
    ): Unit = {
      generatedClasses += generatedClass
    }

    override def onSourceCompiled(source: SourceFile): Unit = {
      compiledSources += source
    }

    def digest(): String = {
      // Sort the files to get a stable hash.
      val sortedFiles = generatedClasses.map(_.jfile).filter(_.isPresent).map(_.get).sorted

      // Collect hash for all files and return it as a string.
      val md = MessageDigest.getInstance("MD5")
      sortedFiles.foreach(jf => digestClassFile(jf, md))
      md.digest().map(b => String.format("%02x", b)).mkString
    }

    private def digestClassFile(jf: File, outputHash: MessageDigest): Unit = {
      val dis = new DigestInputStream(new FileInputStream(jf), outputHash)

      try {
        while (dis.available > 0) {
          dis.read()
        }
      } finally {
        dis.close()
      }
    }
  }
}
