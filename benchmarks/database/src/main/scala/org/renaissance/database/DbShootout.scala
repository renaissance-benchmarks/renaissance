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

import java.io.File
import java.net.URLClassLoader
import java.nio.file.Files
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

  private def buildChronicleClassPath(classPath: String): Seq[Path] = {
    val elements = classPath.split(File.pathSeparatorChar).map(Paths.get(_)).toSeq
    Thread.currentThread.getContextClassLoader match {
      case ucl: URLClassLoader =>
        ucl.getURLs.map(url => Paths.get(url.toURI)).filter { path =>
          val fn = path.getFileName.toString
          fn.startsWith("chronicle-core") || fn.startsWith("chronicle-bytes")
        }
      case _ =>
        // Fall back to current class path.
        // This should be the case in standalone mode.
        elements
    }
  }

  override def setUpBeforeAll(c: BenchmarkContext): Unit = {
    val tempDirPath = c.scratchDirectory()
    val readWriteEntryCountParam = c.parameter("rw_entry_count").toPositiveInteger

    mapDb = new MapDb
    mapDbReader = new MapDb.Reader
    mapDbWriter = new MapDb.Writer
    mapDbReader.setup(tempDirPath.toFile, readWriteEntryCountParam)
    mapDbWriter.setup(tempDirPath.toFile, readWriteEntryCountParam)

    //
    // Chronicle needs the 'java.class.path' property to contain certain jars because
    // it is using the Java compiler to compile generated source code and expects the
    // compiler to find libraries through the normal class path. It is enough to set
    // the property during initialization.
    //
    val oldClassPath = System.getProperty("java.class.path")
    val newClassPath = buildChronicleClassPath(oldClassPath).mkString(File.pathSeparator)
    System.setProperty("java.class.path", newClassPath)

    chronicle = new Chronicle
    chronicleReader = new Chronicle.Reader
    chronicleWriter = new Chronicle.Writer
    chronicleReader.setup(tempDirPath.toFile, readWriteEntryCountParam)
    chronicleWriter.setup(tempDirPath.toFile, readWriteEntryCountParam)

    System.setProperty("java.class.path", oldClassPath)

    mvStore = new MvStore
    mvStoreReader = new MvStore.Reader
    mvStoreWriter = new MvStore.Writer
    mvStoreReader.setup(tempDirPath.toFile, readWriteEntryCountParam)
    mvStoreWriter.setup(tempDirPath.toFile, readWriteEntryCountParam)
  }

  override def tearDownAfterAll(c: BenchmarkContext): Unit = {
    mapDbReader.teardown()
    chronicleReader.teardown()
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
