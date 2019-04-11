package org.renaissance.neo4j

import java.io.File
import java.nio.file.Paths
import org.renaissance.Config
import org.renaissance.License
import org.renaissance.RenaissanceBenchmark
import org.renaissance.neo4j.analytics.AnalyticsBenchmark

class Neo4jAnalytics extends RenaissanceBenchmark {
  def description = "Executes Neo4J graph queries against a movie database."

  def licenses = License.create(License.GPL3)

  // TODO: Unify how the scratch directories are handled, throughout the suite.
  //  See: https://github.com/D-iii-S/renaissance-benchmarks/issues/13
  val scratchPath = Paths.get("target", "modules", "neo4j", "neo4j-analytics.db")

  var benchmark: AnalyticsBenchmark = new AnalyticsBenchmark(scratchPath.toFile)

  override def defaultRepetitions = 10

  override def setUpBeforeAll(c: Config): Unit = {
    benchmark.setupAll()
  }

  override def tearDownAfterAll(c: Config): Unit = {
    benchmark.tearAll()
  }

  protected def runIteration(config: Config): Unit = {
    benchmark.run()
  }
}
