package org.renaissance.database

import java.nio.file.Path

import org.lmdbjava.bench.Chronicle
import org.lmdbjava.bench.MapDb
import org.lmdbjava.bench.MvStore
import org.renaissance.Benchmark
import org.renaissance.Benchmark._
import org.renaissance.BenchmarkContext
import org.renaissance.BenchmarkResult
import org.renaissance.License

@Name("db-shootout")
@Group("database")
@Summary("Executes a shootout test using several in-memory databases.")
@Licenses(Array(License.APACHE2))
@Repetitions(16)
@Parameter(name = "rw_entry_count", defaultValue = "500000")
// Work around @Repeatable annotations not working in this Scala version.
@Configurations(
  Array(
    new Configuration(name = "test", settings = Array("rw_entry_count = 10000")),
    new Configuration(name = "jmh")
  )
)
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

  private var readWriteEntryCountParam: Int = _

  // TODO: Unify handling of scratch directories throughout the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/13

  var tempDirPath: Path = null

  var mapDb: MapDb = null

  var mapDbReader: MapDb.Reader = null

  var mapDbWriter: MapDb.Writer = null

  var chronicle: Chronicle = null

  var chronicleReader: Chronicle.Reader = null

  var chronicleWriter: Chronicle.Writer = null

  var mvStore: MvStore = null

  var mvStoreReader: MvStore.Reader = null

  var mvStoreWriter: MvStore.Writer = null

  override def setUpBeforeAll(c: BenchmarkContext): Unit = {
    tempDirPath = c.generateTempDir("db_shootout")
    readWriteEntryCountParam = c.intParameter("rw_entry_count")

    mapDb = new MapDb
    mapDbReader = new MapDb.Reader
    mapDbWriter = new MapDb.Writer
    mapDbReader.setup(tempDirPath.toFile, readWriteEntryCountParam)
    mapDbWriter.setup(tempDirPath.toFile, readWriteEntryCountParam)

    chronicle = new Chronicle
    chronicleReader = new Chronicle.Reader
    chronicleWriter = new Chronicle.Writer
    chronicleReader.setup(tempDirPath.toFile, readWriteEntryCountParam)
    chronicleWriter.setup(tempDirPath.toFile, readWriteEntryCountParam)

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

    c.deleteTempDir(tempDirPath)
  }

  override def runIteration(c: BenchmarkContext): BenchmarkResult = {
    mapDb.parReadKey(mapDbReader)
    mapDb.parWrite(mapDbWriter)

    chronicle.parReadKey(chronicleReader)
    chronicle.parWrite(chronicleWriter)

    mvStore.parReadKey(mvStoreReader)
    mvStore.parWrite(mvStoreWriter)

    // TODO: add proper validation
    BenchmarkResult.dummy()
  }
}
