package org.renaissance.dbshootout

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
    mapDb = new MapDb
    mapDbWriter = new MapDb.Writer
    mapDbReader = new MapDb.Reader
    mapDbReader.setup()
    mapDbWriter.setup()

    levelDb = new LevelDb
    levelDbWriter = new LevelDb.Writer
    levelDbReader = new LevelDb.Reader
    levelDbReader.setup()
    levelDbWriter.setup()

    chronicle = new Chronicle
    chronicleWriter = new Chronicle.Writer
    chronicleReader = new Chronicle.Reader
    chronicleReader.setup()
    chronicleWriter.setup()

    mvStore = new MvStore
    mvStoreWriter = new MvStore.Writer
    mvStoreReader = new MvStore.Reader
    mvStoreReader.setup()
    mvStoreWriter.setup()
  }

  override def tearDownAfterAll(c: Config): Unit = {
    mapDbReader.teardown()
    levelDbReader.teardown()
    chronicleReader.teardown()
    mvStoreReader.teardown()
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
