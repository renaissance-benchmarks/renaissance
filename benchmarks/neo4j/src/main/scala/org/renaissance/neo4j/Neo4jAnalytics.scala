package org.renaissance.neo4j

import org.neo4j.configuration.GraphDatabaseSettings
import org.neo4j.dbms.api.{DatabaseManagementService, DatabaseManagementServiceBuilder}
import org.neo4j.io.ByteUnit
import org.renaissance.Benchmark._
import org.renaissance.BenchmarkResult.Validators
import org.renaissance.neo4j.analytics.AnalyticsBenchmark
import org.renaissance.neo4j.analytics.AnalyticsBenchmark._
import org.renaissance.{Benchmark, BenchmarkContext, BenchmarkResult, License}
import play.api.libs.json._

import java.nio.file.{Files, Path}
import java.util.concurrent.atomic.AtomicReference
import scala.io.{Codec, Source}

@Name("neo4j-analytics")
@Group("database")
@Group("neo4j")
@Summary("Executes Neo4j graph queries against a movie database.")
@Licenses(Array(License.GPL3))
@RequiresJvm("17")
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

  /*
   * Methods for reading JSON data.
   */
  private def extractVertices(values: Iterable[JsValue]): Iterable[Vertex] = {
    implicit val givenGenreReads: Reads[Genre] = Json.reads[Genre]
    implicit val givenDirectorReads: Reads[Director] = Json.reads[Director]
    implicit val givenFilmReads: Reads[Film] = Json.reads[Film]

    values.map { v =>
      try {
        (v \ "label").as[String] match {
          case "Genre" => v.as[Genre]
          case "Film" => v.as[Film]
          case "Director" => v.as[Director]
          case _ => ???
        }
      } catch {
        case _: JsResultException =>
          sys.error(s"Failed to extract vertex from $v")
      }
    }
  }

  private def extractEdges(values: Iterable[JsValue]): Iterable[Edge] = {
    implicit val givenEdgeReads: Reads[Edge] = Json.reads[Edge]

    values.map { v =>
      try {
        v.as[Edge]
      } catch {
        case _: JsResultException =>
          sys.error(s"Failed to extract edge from $v")
      }
    }
  }

  private def loadJsonResource(name: String): Iterable[JsValue] = {
    implicit val givenSourceCodec: Codec = Codec.UTF8
    val source = Source.createBufferedSource(getClass.getResourceAsStream(name))
    Json.parse(source.mkString).as[JsArray].value
  }

  override def setUpBeforeAll(c: BenchmarkContext): Unit = {

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

    println("Loading resources...")
    val vertices = extractVertices(loadJsonResource("/vertices.json"))
    val edges = extractEdges(loadJsonResource("/edges.json"))

    benchmark.populateDatabase(vertices, edges)

    expectedQueryCount = benchmark.totalQueryCount()
  }

  override def run(c: BenchmarkContext): BenchmarkResult = {
    val actualQueryCount = benchmark.run().toLong
    Validators.simple("NumSuccessfulQueries", expectedQueryCount, actualQueryCount)
  }

  override def tearDownAfterAll(c: BenchmarkContext): Unit = {
    shutdownDatabaseOnce()
  }

  private def createGraphDatabase(graphDbDir: Path) = {
    println("Creating graph database...")
    Files.createDirectory(graphDbDir)

    dbms.set(
      new DatabaseManagementServiceBuilder(graphDbDir)
        .setConfig(GraphDatabaseSettings.pagecache_memory, Long.box(ByteUnit.mebiBytes(512)))
        .build()
    )

    Runtime.getRuntime.addShutdownHook(new Thread {
      override def run(): Unit = shutdownDatabaseOnce()
    })

    dbms.get().database(GraphDatabaseSettings.DEFAULT_DATABASE_NAME)
  }

  private def shutdownDatabaseOnce(): Unit = {
    Option(dbms.getAndSet(null)).foreach(_.shutdown())
  }

}
