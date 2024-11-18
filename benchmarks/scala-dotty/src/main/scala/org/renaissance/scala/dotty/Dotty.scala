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
import org.renaissance.License
import org.renaissance.core.DirUtils

import java.io.File
import java.io.FileInputStream
import java.net.URLClassLoader
import java.nio.file.Files
import java.nio.file.Files.copy
import java.nio.file.Files.createDirectories
import java.nio.file.Files.notExists
import java.nio.file.Path
import java.nio.file.Paths
import java.nio.file.StandardCopyOption.REPLACE_EXISTING
import java.security.DigestInputStream
import java.security.MessageDigest
import java.util.jar
import java.util.jar.Attributes
import java.util.jar.JarFile
import java.util.zip.ZipInputStream
import scala.collection._

@Name("dotty")
@Group("scala-dotty")
@Group("scala") // With Scala 3, the primary group goes last.
@Summary("Runs the Dotty compiler on a set of source code files.")
@Licenses(Array(License.BSD3))
@Repetitions(50)
@Configuration(name = "test")
@Configuration(name = "jmh")
final class Dotty extends Benchmark {

  // TODO: Consolidate benchmark parameters across the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/27

  /**
   * MD5 digest of all generated .tasty files (except a few which embed
   * the current working directory path into the .tasty file).
   *
   * find . -type f -name '*.tasty'|egrep -v '(Classfile|ByteCode)\.tasty' | LC_ALL=C sort|xargs cat|md5sum
   */
  private val expectedTastyHash: String = "5c33664eacffb74f853dec92efd9d503"

  private val excludedTastyFiles = Seq("Classfile.tasty", "ByteCode.tasty")

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
     * Dotty is unable to use the current class loader (either of this class
     * or this thread), and passing the class loader to the compiler seems to
     * be impossible with the current API (see the discussion at
     * https://github.com/renaissance-benchmarks/renaissance/issues/176).
     *
     * So we instead pass the class path as a command line option. Note that
     * the '-usejavacp' option does not help, because it reads from the
     * 'java.class.path' system property, which does not contain anything
     * useful and we do not want to modify it here.
     *
     * However, constructing the class path is a bit involved.
     * See the [[buildDottyClassPath]] method for details.
     */
    val dottyClassPath = buildDottyClassPath(System.getProperty("java.class.path"))

    val scratchDir = bc.scratchDirectory()
    val sourceDir = scratchDir.resolve("src")
    val sourceFiles = unzipResource(sourcesInputResource, sourceDir)

    dottyOutputDir = createDirectories(scratchDir.resolve("out"))

    val dottyBaseArgs = Seq[String](
      // Mark the sources as transitional.
      "-source",
      "3.0-migration",
      // Class path with dependency jars.
      "-classpath",
      dottyClassPath.mkString(File.pathSeparator),
      // Output directory for compiled baseFiles.
      "-d",
      dottyOutputDir.toString,
      // Setting source root makes the .tasty files idempotent between repetitions.
      "-sourceroot",
      sourceDir.toString
    )

    // Compile all sources as a single batch.
    dottyArgs = (dottyBaseArgs ++ sourceFiles.map(_.toString)).toArray
  }

  private def buildDottyClassPath(classPath: String): Seq[Path] = {
    /*
     * If we are running with module loading enabled, we know that our class
     * loader will be an instance of URLClassLoader which loads the benchmark
     * JARs from a temporary directory. In that case, we can just convert all
     * the URLs to plain file paths.
     *
     * Note that using the URLs directly is not possible, because they
     * contain the "file://" protocol prefix, which is not handled well
     * on Windows (when on the classpath).
     *
     * If we are running in standalone mode, the class loader may or may not
     * be an URLClassloader instance and even if it is, it will not contain
     * anything useful. In that case, we read the manifest from the jar file
     * referenced by 'java.class.path' and construct the class path using the
     * value of the 'Class-Path' attribute.
     */
    def loadJarManifest(jarPath: Path) = {
      val jarFile = new JarFile(jarPath.toFile)
      try {
        jarFile.getManifest
      } finally {
        jarFile.close()
      }
    }

    def classPathFromManifest(jmf: jar.Manifest, base: Path) = {
      jmf.getMainAttributes
        .getValue(Attributes.Name.CLASS_PATH)
        .split(" ")
        .map(path => base.resolveSibling(path).normalize())
        .toSeq
    }

    //
    // If the current class path consists solely of 'dotty.jar', try
    // to build the class path from the jar manifest, otherwise try to
    // get URLs from the class loader. If even that fails (we may be
    // running without module loading with all jars specified on the
    // command line), fall back to the current class path.
    //
    val classPathElements = classPath.split(File.pathSeparatorChar).map(Paths.get(_))
    if (classPathElements.length == 1) {
      val singleJar = classPathElements.head
      if (!Files.isDirectory(singleJar) && singleJar.endsWith("dotty.jar")) {
        // We are probably running in 'java -jar' mode.
        val mf = loadJarManifest(singleJar)
        return classPathFromManifest(mf, singleJar)
      }
    }

    Thread.currentThread.getContextClassLoader match {
      case ucl: URLClassLoader =>
        ucl.getURLs.map(url => Paths.get(url.toURI)).toSeq
      case _ =>
        // Fall back to current class path.
        classPathElements
    }
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
          val pos = d.position().map[String](p => s"${p.source()}:${p.line()}: ").orElse("")
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

  // Enforce lexicographic ordering (LC_ALL=C style) on file names. Even though
  // File instances are (lexicographically) Comparable, they use a file-system
  // specific ordering which may ignore character case (e.g., on Windows).
  object AsciiFileOrdering extends Ordering[File] {
    def compare(a: File, b: File): Int = a.toString.compareTo(b.toString)
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
      // Compute hash for selected files and return it as a string.
      val md = MessageDigest.getInstance("MD5")
      tastyFilesFor(generatedClasses).foreach(digestFile(_, md))
      md.digest().map(String.format("%02x", _)).mkString
    }

    private def tastyFilesFor(classFiles: mutable.Seq[AbstractFile]) = {
      //
      // Create a sorted list of .tasty files corresponding to .class files.
      // The filtering based on the presence of the '$' character is a bit ad-hoc,
      // because (unfortunately) some .tasty file names contain the '$' character.
      // Right now we assume that '$' can only appear as first letter, just like
      // in the '$tilde.tasty' file. The goal is to get a list of files that should
      // exist, not to filter out files that do not exist.
      // Note that we need to sort them in platform-independent way
      // (i.e., in the "C" locale).
      //
      classFiles
        .flatMap(_.jfile().map[Option[File]](f => Some(f)).orElse(None))
        .filter(_.getName.lastIndexOf('$') < 1)
        .map(file => {
          val fileName = file.getName
          val dotIndex = fileName.lastIndexOf('.')
          val baseName = if (dotIndex > 0) fileName.substring(0, dotIndex) else fileName
          val tastyName = s"${baseName}.tasty"
          new File(file.getParentFile(), tastyName)
        })
        .filterNot(f => excludedTastyFiles.contains(f.getName))
        .sorted(AsciiFileOrdering)
    }

    private def digestFile(file: File, outputHash: MessageDigest): Unit = {
      val dis = new DigestInputStream(new FileInputStream(file), outputHash)

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
