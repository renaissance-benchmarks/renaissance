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
  name = "expected_tasty_hash",
  // find . -type f -name '*.tasty'|LC_ALL=C sort|xargs cat|md5sum"
  defaultValue = "0cc9c04f580b3ad28123101c89a83c48",
  summary = "MD5 digest of all generated .tasty files"
)
@Configuration(name = "test")
@Configuration(name = "jmh")
final class Dotty extends Benchmark {

  // TODO: Consolidate benchmark parameters across the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/27

  private var expectedTastyHash: String = _

  private val sourcesInputResource = "/scalap.zip"

  private var dottyOutputDir: Path = _

  private var dottyArgs: Array[String] = _

  /** Show Dotty compilation warnings during validation. For debugging only. */
  private val showDottyWarnings = false

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
      .map(url => new File(url.toURI).getPath)
      .toBuffer

    val scratchDir = bc.scratchDirectory()
    dottyOutputDir = createDirectories(scratchDir.resolve("out"))

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
      dottyOutputDir.toString,
      // Setting the root of the sources directory stabilizes the contents of .tasty files.
      "-sourceroot",
      sourceDir.toString
    )

    // Compile all sources as a single batch.
    dottyArgs = (dottyBaseArgs ++ sourceFiles.map(_.toString)).toArray

    expectedTastyHash = bc.parameter("expected_tasty_hash").value()
  }

  override def setUpBeforeEach(bc: BenchmarkContext): Unit = {
    //
    // Clean the Dotty output directory to make sure that it
    // always produces all the files. Alternatively, we could
    // create a new output directory for each repetition.
    //
    DirUtils.cleanRecursively(dottyOutputDir)
  }

  override def run(bc: BenchmarkContext): BenchmarkResult = {
    val result = new CompilationResult
    DottyMain.process(dottyArgs, result, result)

    () => {
      def printDiagnostics(diags: mutable.Buffer[Diagnostic], prefix: String) = {
        diags.foreach(d => {
          val pos = d.position().map(p => s"${p.source()}:${p.line()}: ").orElse("")
          println(s"${prefix}: ${pos}${d.message()}")
        })
      }

      //
      // There may be warnings due to the transitional nature of the compiled
      // sources, but they do not render the benchmark result invalid. There
      // is no need to display them unless enabled for debugging.
      //
      if (showDottyWarnings) {
        printDiagnostics(result.warnings, "dotty-warning")
      }

      //
      // There must be no errors for the result to be considered valid.
      // We do show the errors before failing.
      //
      printDiagnostics(result.errors, "dotty-error")
      Assert.assertEquals(0, result.errors.length, "compilation errors")

      //
      // We checksum the generated .tasty files, because the .class files are
      // not byte-exact between Renaissance builds. Even for the .tasty files,
      // we need to pass the '-sourceroot' option to the compiler so that it
      // avoids storing some sort of source-path hash into the output.
      //
      Assert.assertEquals(expectedTastyHash, result.digest(), "digest of generated tasty files")
    }
  }

  private class CompilationResult extends SimpleReporter with CompilerCallback {
    val errors = mutable.Buffer[Diagnostic]()
    val warnings = mutable.Buffer[Diagnostic]()

    override def report(diag: Diagnostic): Unit = {
      diag.level() match {
        case Diagnostic.ERROR => errors += diag
        case Diagnostic.WARNING => warnings += diag
        case _ => /* ignore */
      }
    }

    val generatedClasses = mutable.Buffer[AbstractFile]()

    override def onClassGenerated(
      source: SourceFile,
      generatedClass: AbstractFile,
      className: String
    ): Unit = {
      generatedClasses += generatedClass
    }

    def digest(): String = {
      //
      // Create a sorted list of .tasty files corresponding to .class files.
      // The filtering based on the presence of the '$' character is a bit ad-hoc,
      // because (unfortunately) some tasty files can contain the '$' character.
      // Right now we assume that they can only start with '$', just like the
      // '$tilde.tasty' file. The goal is to get a list of files that should
      // exist, not to filter files that do not exist.
      //
      val tastyFiles = generatedClasses
        .filter(_.jfile().isPresent)
        .map(_.jfile().get())
        .filter(_.getName.lastIndexOf('$') < 1)
        .map(file => {
          val fileName = file.getName
          val dotIndex = fileName.lastIndexOf('.')
          val baseName = if (dotIndex > 0) fileName.substring(0, dotIndex) else fileName
          val tastyName = s"${baseName}.tasty"
          new File(file.getParentFile(), tastyName)
        })
        .sorted

      // Compute hash for all .tasty files and return it as a string.
      val md = MessageDigest.getInstance("MD5")
      tastyFiles.foreach(jf => digestFile(jf, md))
      md.digest().map(b => String.format("%02x", b)).mkString
    }

    private def digestFile(jf: File, outputHash: MessageDigest): Unit = {
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
