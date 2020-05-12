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
// Work around @Repeatable annotations not working in this Scala version.
@Parameters(
  Array(
    new Parameter(name = "recompilation_count", defaultValue = "1"),
    new Parameter(name = "batch_size", defaultValue = "8")
  )
)
@Configurations(
  Array(
    new Configuration(name = "test", settings = Array("recompilation_count = 1", "batch_size = 50")),
    new Configuration(name = "no-batch", settings = Array("recompilation_count = 1", "batch_size = 1")),
    new Configuration(name = "large", settings = Array("recompilation_count = 2", "batch_size = 4")),
    new Configuration(name = "jmh")
  )
)
final class JdtCompiler extends Benchmark {

  // TODO: Consolidate benchmark parameters across the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/27


  private var recompilationCountParam: Int = _

  private var batchSizeParam: Int = _

  private val dumpClassFiles = false

  private val parallelizationLevel: Int = 1

  private val zipPath = "algorithms.zip"

  private val ecjPath = Paths.get("target", "ecj")

  private val sourceCodePath = ecjPath.resolve("src")

  private val outputPath = ecjPath.resolve("output")

  private val sources: mutable.Buffer[String] = mutable.Buffer[String]()

  private var sourcePaths: mutable.Buffer[String] = _

  private def unzipSources(): Unit = {
    val zis = new ZipInputStream(this.getClass.getResourceAsStream("/" + zipPath))

    Stream.continually(zis.getNextEntry).takeWhile(_ != null).foreach { file =>
      if (!file.isDirectory) {
        val outPath = sourceCodePath.resolve(file.getName)
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
    sourcePaths = sources.map(f => sourceCodePath.resolve(f).toString).filter(f => f.endsWith(".java"))
  }

  override def setUpBeforeAll(c: BenchmarkContext): Unit = {
    recompilationCountParam = c.intParameter("recompilation_count")
    batchSizeParam = c.intParameter("batch_size")

    outputPath.toFile.mkdirs()
    unzipSources()
    setUpSourcePaths()
    // generate all class files once, such that we can incrementally rebuild any file without missing dependency
    BatchCompiler.compile(
      ecjArgs(true).toArray ++ sourcePaths,
      new PrintWriter(new StringWriter),
      new PrintWriter(new StringWriter),
      null
    )
    //BatchCompiler.compile("-help", new PrintWriter(System.out), new PrintWriter(System.err), null)
  }

  private def ecjArgs(dump: Boolean): Seq[String] = {
    /*
     * The same trick that is being used for the Dotty benchmark is required here.
     * For context, see https://github.com/renaissance-benchmarks/renaissance/issues/176.
     */
    val generatedClasspath = (Thread.currentThread.getContextClassLoader
      .asInstanceOf[URLClassLoader]
      .getURLs
      .map(url => new java.io.File(url.toURI).getPath) ++ List(outputPath, sourceCodePath))
      .mkString(File.pathSeparator)

    Seq[String](
      ECJ_ARG_NOWARN,
      ECJ_ARG_REPEAT,
      recompilationCountParam.toString,
      ECJ_ARG_TARGET,
      ECJ_ARG_TARGET_VERSION,
      ECJ_ARG_COMPLIANCE_LEVEL,
      //ECJ_ARG_ADD_MODULES, // only works on more recent ecj versions that support JDK9+ (unfortunately not on maven)
      ECJ_ARG_CLASS_PATH,
      generatedClasspath,
      ECJ_ARG_CLASS_FILE_DESTINATION,
      if (dump) outputPath.toString else "none"
    )
  }

  private val ECJ_ARG_NOWARN = "-warn:none"

  private val ECJ_ARG_REPEAT = "-repeat"

  private val ECJ_ARG_TARGET = "-target"

  private val ECJ_ARG_TARGET_VERSION = "1.9"

  private val ECJ_ARG_COMPLIANCE_LEVEL = "-1.9"

  private val ECJ_ARG_CLASS_PATH = "-classpath"

  private val ECJ_ARG_ADD_MODULES = "--add-modules=ALL-SYSTEM"

  private val ECJ_ARG_CLASS_FILE_DESTINATION = "-d"

  override def run(c: BenchmarkContext): BenchmarkResult = {
    val stdout = new StringWriter
    val stderr = new StringWriter

    val batches = sourcePaths.grouped(batchSizeParam).toList

    val successCount = if (parallelizationLevel > 1)
      batches.par.map(fileSet => {
        BatchCompiler.compile(
          ecjArgs(dumpClassFiles).toArray ++ fileSet,
          new PrintWriter(stdout),
          new PrintWriter(stderr),
          null
        )
      }).seq.count(_ == true)
    else
      batches.map(fileSet => {
        BatchCompiler.compile(
          ecjArgs(dumpClassFiles).toArray ++ fileSet,
          new PrintWriter(stdout),
          new PrintWriter(stderr),
          null
        )
      }).count(_ == true)

      if (successCount < batches.size || stderr.toString.length > 0) {
        println("stdout :")
        println(stdout.toString)
        println("stderr :")
        println(stderr.toString)
      }
    Validators.compound(
      Validators.simple("ECJ compilations must all succeed", batches.size, successCount),
      Validators.simple("Standard error must be of size zero", 0, stderr.toString.length)
    )
  }
}
