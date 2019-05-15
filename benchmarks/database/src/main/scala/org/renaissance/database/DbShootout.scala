package org.renaissance.database

import java.nio.file.Path

import org.lmdbjava.bench.Chronicle
import org.lmdbjava.bench.LevelDb
import org.lmdbjava.bench.MapDb
import org.lmdbjava.bench.MvStore
import org.renaissance.Benchmark._
import org.renaissance.Config
import org.renaissance.License
import org.renaissance.RenaissanceBenchmark

@Name("db-shootout")
@Group("database")
@Summary("Executes a shootout test using several in-memory databases.")
@Licenses(Array(License.APACHE2))
@Repetitions(16)
class DbShootout extends RenaissanceBenchmark {

  /**
   * The original benchmarks are from https://github.com/lmdbjava/benchmarks
   * and have been slightly adapted.
   * For instance, the JMH dependency has been removed and the location where
   * the benchmark writes on disk has been updated to match the rest of the
   * renaissance suite.
   */
  // TODO: Consolidate benchmark parameters across the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/27

  var numEntriesToReadWrite: Int = 500000

  // TODO: Unify handling of scratch directories throughout the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/13

  var tempDirPath: Path = null

  var mapDb: MapDb = null

  var mapDbReader: MapDb.Reader = null

  var mapDbWriter: MapDb.Writer = null

  var levelDb: LevelDb = null

  var levelDbReader: LevelDb.Reader = null

  var levelDbWriter: LevelDb.Writer = null

  var chronicle: Chronicle = null

  var chronicleReader: Chronicle.Reader = null

  var chronicleWriter: Chronicle.Writer = null

  var mvStore: MvStore = null

  var mvStoreReader: MvStore.Reader = null

  var mvStoreWriter: MvStore.Writer = null

  override def setUpBeforeAll(c: Config): Unit = {
    tempDirPath = RenaissanceBenchmark.generateTempDir("db_shootout")

    if (c.functionalTest) {
      numEntriesToReadWrite = 10000
    }

    mapDb = new MapDb
    mapDbReader = new MapDb.Reader
    mapDbWriter = new MapDb.Writer
    mapDbReader.setup(tempDirPath.toFile, numEntriesToReadWrite)
    mapDbWriter.setup(tempDirPath.toFile, numEntriesToReadWrite)

    levelDb = new LevelDb
    levelDbReader = new LevelDb.Reader
    levelDbWriter = new LevelDb.Writer
    levelDbReader.setup(tempDirPath.toFile, numEntriesToReadWrite)
    levelDbWriter.setup(tempDirPath.toFile, numEntriesToReadWrite)

    chronicle = new Chronicle
    chronicleReader = new Chronicle.Reader
    chronicleWriter = new Chronicle.Writer
    chronicleReader.setup(tempDirPath.toFile, numEntriesToReadWrite)
    chronicleWriter.setup(tempDirPath.toFile, numEntriesToReadWrite)

    mvStore = new MvStore
    mvStoreReader = new MvStore.Reader
    mvStoreWriter = new MvStore.Writer
    mvStoreReader.setup(tempDirPath.toFile, numEntriesToReadWrite)
    mvStoreWriter.setup(tempDirPath.toFile, numEntriesToReadWrite)
  }

  override def tearDownAfterAll(c: Config): Unit = {
    mapDbReader.teardown()
    levelDbReader.teardown()
    chronicleReader.teardown()
    mvStoreReader.teardown()

    RenaissanceBenchmark.deleteTempDir(tempDirPath)
  }

  def runIteration(c: Config): Unit = {
    mapDb.parReadKey(mapDbReader)
    mapDb.parWrite(mapDbWriter)

    levelDb.parReadKey(levelDbReader)
    levelDb.parWrite(levelDbWriter)

    chronicle.parReadKey(chronicleReader)
    chronicle.parWrite(chronicleWriter)

    mvStore.parReadKey(mvStoreReader)
    mvStore.parWrite(mvStoreWriter)
  }
}
