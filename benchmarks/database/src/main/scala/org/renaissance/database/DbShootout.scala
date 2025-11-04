package org.renaissance.database

import org.lmdbjava.bench.Chronicle
import org.lmdbjava.bench.MapDb
import org.lmdbjava.bench.MvStore

import org.renaissance.Benchmark
import org.renaissance.Benchmark._
import org.renaissance.BenchmarkContext
import org.renaissance.BenchmarkResult
import org.renaissance.BenchmarkResult.Validators
import org.renaissance.License
import org.renaissance.core.ResourceUtils

import java.io.File
import java.net.URL
import java.net.URLClassLoader
import java.nio.file.Files
import java.nio.file.Files.createDirectories
import java.nio.file.Path
import java.nio.file.Paths
import scala.collection.Seq

@Name("db-shootout")
@Group("database")
@Summary("Executes a shootout test using several in-memory databases.")
@Licenses(Array(License.APACHE2))
@Repetitions(16)
@Parameter(name = "rw_entry_count", defaultValue = "500000")
@Configuration(name = "test", settings = Array("rw_entry_count = 10000"))
@Configuration(name = "jmh")
final class DbShootout extends Benchmark {

  /**
   * The original benchmarks are from https://github.com/lmdbjava/benchmarks
   * and have been slightly adapted.
   * For instance, the JMH dependency has been removed and the location where
   * the benchmark writes on disk has been updated to match the rest of the
   * renaissance suite.
   */
  // TODO: Consolidate benchmark parameters across the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/27

  var mapDb: MapDb = _

  var mapDbReader: MapDb.Reader = _

  var mapDbWriter: MapDb.Writer = _

  var chronicle: Chronicle = _

  var chronicleReader: Chronicle.Reader = _

  var chronicleWriter: Chronicle.Writer = _

  var mvStore: MvStore = _

  var mvStoreReader: MvStore.Reader = _

  var mvStoreWriter: MvStore.Writer = _

  private def buildChronicleClassPath(classPath: String, libDir: Path): Seq[String] = {
    //
    // If this class was loaded by a URLClassLoader, get the JAR file
    // resource URLs, extract them into a library directory and build
    // the class path from the extracted files.
    //
    // Otherwise, fall back to the current class path (we may be running
    // without module loading with all jars specified on the command line).
    //
    getClass.getClassLoader match {
      case ucl: URLClassLoader =>
        import scala.jdk.CollectionConverters._

        val resourcePaths = ucl.getURLs
          .map(_.getPath)
          .filter { path =>
            path.contains("chronicle-core") || path.contains("chronicle-bytes")
          }
          .toIterable
          .asJava

        Files.createDirectories(libDir)
        val jarPaths = ResourceUtils.extractResources(resourcePaths, libDir)
        jarPaths.asScala.map(_.toString)
      case _ =>
        // Fall back to current class path.
        classPath.split(File.pathSeparatorChar)
    }
  }

  override def setUpBeforeAll(c: BenchmarkContext): Unit = {
    val tempDirPath = c.scratchDirectory()
    val readWriteEntryCountParam = c.parameter("rw_entry_count").toPositiveInteger

    mapDb = new MapDb
    val mapDbScratch = createDirectories(tempDirPath.resolve("mapdb")).toFile

    mapDbReader = new MapDb.Reader
    mapDbReader.setup(mapDbScratch, readWriteEntryCountParam)
    mapDbWriter = new MapDb.Writer
    mapDbWriter.setup(mapDbScratch, readWriteEntryCountParam)

    //
    // Chronicle Map 3.20.84 started connecting to Google Analytics in an
    // extra thread (see https://github.com/OpenHFT/Chronicle-Map/issues/247).
    // This is not something we want, so we disable it.
    //
    System.setProperty("chronicle.analytics.disable", "true")

    //
    // Chronicle needs the 'java.class.path' property to contain certain jars because
    // it is using the Java compiler to compile generated source code and expects the
    // compiler to find libraries through the normal class path. It is enough to set
    // the property during initialization.
    //
    // Because we load jars from resources, we need to extract them first so that
    // the Java compiler can find them.
    //
    val oldClassPath = System.getProperty("java.class.path")

    val newClassPathElements = buildChronicleClassPath(oldClassPath, tempDirPath.resolve("lib"))
    System.setProperty("java.class.path", newClassPathElements.mkString(File.pathSeparator))

    chronicle = new Chronicle
    val chronicleScratch = createDirectories(tempDirPath.resolve("chronicle")).toFile

    chronicleReader = new Chronicle.Reader
    chronicleReader.setup(chronicleScratch, readWriteEntryCountParam)
    chronicleWriter = new Chronicle.Writer
    chronicleWriter.setup(chronicleScratch, readWriteEntryCountParam)

    System.setProperty("java.class.path", oldClassPath)

    mvStore = new MvStore
    val mvStoreScratch = createDirectories(tempDirPath.resolve("mvstore")).toFile

    mvStoreReader = new MvStore.Reader
    mvStoreReader.setup(mvStoreScratch, readWriteEntryCountParam)
    mvStoreWriter = new MvStore.Writer
    mvStoreWriter.setup(mvStoreScratch, readWriteEntryCountParam)
  }

  override def tearDownAfterAll(c: BenchmarkContext): Unit = {
    mapDbWriter.teardown()
    mapDbReader.teardown()

    chronicleWriter.teardown()
    chronicleReader.teardown()

    mvStoreWriter.teardown()
    mvStoreReader.teardown()
  }

  override def run(c: BenchmarkContext): BenchmarkResult = {
    mapDb.parReadKey(mapDbReader)
    mapDb.parWrite(mapDbWriter)

    chronicle.parReadKey(chronicleReader)
    chronicle.parWrite(chronicleWriter)

    mvStore.parReadKey(mvStoreReader)
    mvStore.parWrite(mvStoreWriter)

    // TODO: add proper validation
    Validators.dummy()
  }
}
