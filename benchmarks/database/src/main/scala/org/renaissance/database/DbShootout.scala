package org.renaissance.database

import java.nio.file.Path

import org.lmdbjava.bench.{Chronicle, LevelDb, MapDb, MvStore}
import org.renaissance.{Config, License, RenaissanceBenchmark}

class DbShootout extends RenaissanceBenchmark {

  /**
   * The original benchmarks are from https://github.com/lmdbjava/benchmarks
   * and have been slightly adapted.
   * For instance, the JMH dependency has been removed and the location where
   * the benchmark writes on disk has been updated to match the rest of the
   * renaissance suite.
   */
  override def description(): String =
    "Executes a shootout test using several in-memory databases."

  def licenses = License.create(License.APACHE2)

  override def defaultRepetitions = 16

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

    mapDb = new MapDb
    mapDbReader = new MapDb.Reader
    mapDbWriter = new MapDb.Writer
    mapDbReader.setup(tempDirPath.toFile)
    mapDbWriter.setup(tempDirPath.toFile)

    levelDb = new LevelDb
    levelDbReader = new LevelDb.Reader
    levelDbWriter = new LevelDb.Writer
    levelDbReader.setup(tempDirPath.toFile)
    levelDbWriter.setup(tempDirPath.toFile)

    chronicle = new Chronicle
    chronicleReader = new Chronicle.Reader
    chronicleWriter = new Chronicle.Writer
    chronicleReader.setup(tempDirPath.toFile)
    chronicleWriter.setup(tempDirPath.toFile)

    mvStore = new MvStore
    mvStoreReader = new MvStore.Reader
    mvStoreWriter = new MvStore.Writer
    mvStoreReader.setup(tempDirPath.toFile)
    mvStoreWriter.setup(tempDirPath.toFile)
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
