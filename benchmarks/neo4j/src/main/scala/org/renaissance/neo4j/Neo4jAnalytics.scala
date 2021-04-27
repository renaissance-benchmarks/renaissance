package org.renaissance.neo4j

import org.neo4j.configuration.GraphDatabaseSettings
import org.neo4j.dbms.api.{DatabaseManagementService, DatabaseManagementServiceBuilder}
import org.neo4j.logging.Level
import org.renaissance.Benchmark._
import org.renaissance.BenchmarkResult.Validators
import org.renaissance.neo4j.analytics.AnalyticsBenchmark
import org.renaissance.{Benchmark, BenchmarkContext, BenchmarkResult, License}

import java.nio.file.{Files, Path}
import java.util.concurrent.atomic.AtomicReference
import scala.io.{Codec, Source}

@Name("neo4j-analytics")
@Group("neo4j")
@Summary("Executes Neo4J graph queries against a movie database.")
@Licenses(Array(License.GPL3))
@RequiresJvm("11")
@SupportsJvm("15")
@Repetitions(20)
@Parameter(name = "long_query_threads", defaultValue = "2")
@Parameter(name = "long_query_repeats", defaultValue = "1")
@Parameter(name = "short_query_threads", defaultValue = "1")
@Parameter(name = "short_query_repeats", defaultValue = "150")
@Parameter(name = "mutator_query_threads", defaultValue = "1")
@Parameter(name = "mutator_query_repeats", defaultValue = "12")
@Configuration(name = "test")
@Configuration(name = "jmh")
final class Neo4jAnalytics extends Benchmark {

  // TODO: Consolidate benchmark parameters across the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/27

  private var benchmark: AnalyticsBenchmark = _

  private var expectedQueryCount: Int = _

  private val dbms = new AtomicReference[DatabaseManagementService]()

  override def setUpBeforeAll(c: BenchmarkContext): Unit = {
    def loadResource(name: String) = {
      implicit val defaultCodec = Codec.UTF8
      Source.createBufferedSource(getClass.getResourceAsStream(name))
    }

    val graphDbDir = c.scratchDirectory().resolve("graphdb").normalize()
    val graphDb = createGraphDatabase(graphDbDir)

    benchmark = new AnalyticsBenchmark(
      graphDb,
      c.parameter("long_query_threads").toPositiveInteger,
      c.parameter("long_query_repeats").toPositiveInteger,
      c.parameter("short_query_threads").toPositiveInteger,
      c.parameter("short_query_repeats").toPositiveInteger,
      c.parameter("mutator_query_threads").toPositiveInteger,
      c.parameter("mutator_query_repeats").toPositiveInteger
    )

    benchmark.populateDatabase(
      loadResource("/vertices.json"),
      loadResource("/edges.json")
    )

    expectedQueryCount = benchmark.totalQueryCount()
  }

  override def run(c: BenchmarkContext): BenchmarkResult = {
    val actualQueryCount = benchmark.run().toLong
    Validators.simple("NumSuccessfulQueries", expectedQueryCount, actualQueryCount)
  }

  override def tearDownAfterAll(c: BenchmarkContext): Unit = {
    shutdownDatabaseOnce
  }

  private def createGraphDatabase(graphDbDir: Path) = {
    println("Creating graph database...")
    Files.createDirectory(graphDbDir)

    dbms.set(
      new DatabaseManagementServiceBuilder(graphDbDir)
        .setConfig(GraphDatabaseSettings.pagecache_memory, "500M")
        .setConfig(GraphDatabaseSettings.store_internal_log_level, Level.WARN)
        .build()
    )

    Runtime.getRuntime.addShutdownHook(new Thread {
      override def run(): Unit = shutdownDatabaseOnce
    })

    dbms.get().database(GraphDatabaseSettings.DEFAULT_DATABASE_NAME)
  }

  private def shutdownDatabaseOnce: Unit = {
    Option(dbms.getAndSet(null)).foreach(_.shutdown())
  }

}
