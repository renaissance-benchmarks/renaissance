package org.renaissance.neo4j

import java.io.File
import org.renaissance.Config
import org.renaissance.License
import org.renaissance.RenaissanceBenchmark
import org.renaissance.neo4j.analytics.AnalyticsBenchmark

class Neo4jAnalytics extends RenaissanceBenchmark {
  def description = "Executes Neo4J graph queries against a movie database."

  def licenses = License.create(License.GPL3)

  var benchmark: AnalyticsBenchmark = null

  // TODO: Unify how the scratch directories are handled, throughout the suite.
  //  See: https://github.com/D-iii-S/renaissance-benchmarks/issues/13
  val scratchPath = "target/modules/neo4j"

  override def defaultRepetitions = 10

  override def setUpBeforeAll(c: Config): Unit = {
    val dbFileName = "neo4j-analytics.db"
    benchmark = new AnalyticsBenchmark(new File(s"$scratchPath/$dbFileName"))
  }

  override def tearDownAfterAll(c: Config): Unit = {
    benchmark.tearAll()
  }

  protected def runIteration(config: Config): Unit = {
    benchmark.run()
  }
}
