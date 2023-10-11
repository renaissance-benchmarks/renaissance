package org.renaissance.neo4j.analytics

import org.neo4j.graphdb.{GraphDatabaseService, Label, RelationshipType, Result}
import org.renaissance.neo4j.analytics.AnalyticsBenchmark._

import java.util.concurrent.TimeUnit
import scala.jdk.CollectionConverters._
import scala.collection.{Seq, _}

/*
 * Model of JSON data.
 */
object AnalyticsBenchmark {

  private type VertexId = Int

  trait Vertex {
    def id: VertexId

    def label: String
  }

  case class Genre(id: VertexId, label: String, genreId: String, name: String) extends Vertex

  case class Film(
    id: VertexId,
    label: String,
    filmId: String,
    name: String,
    releaseDate: String
  ) extends Vertex

  case class Director(id: VertexId, label: String, directorId: String, name: String)
    extends Vertex

  case class Edge(source: VertexId, destination: VertexId, label: String)
}

class AnalyticsBenchmark(
  private val graphDb: GraphDatabaseService,
  private val longQueryThreads: Int,
  private val longQueryRepeats: Int,
  private val shortQueryThreads: Int,
  private val shortQueryRepeats: Int,
  private val mutatorQueryThreads: Int,
  private val mutatorQueryRepeats: Int
) {

  /**
   * Populates the database with data. Must be called before `run()`.
   */
  def populateDatabase(vertices: Iterable[Vertex], edges: Iterable[Edge]): Unit = {
    println("Populating database...")
    val vertexNodeIds = populateVertices(graphDb, vertices)
    val edgeCount = populateEdges(graphDb, edges, vertexNodeIds)

    println("Creating indices...")
    createIndices(graphDb)

    println(s"Database initialized with ${vertexNodeIds.size} vertices and $edgeCount edges.")
  }

  private def populateVertices(
    db: GraphDatabaseService,
    vertices: Iterable[Vertex]
  ): Map[VertexId, String] = {
    val mapping = mutable.Map[VertexId, String]()

    val tx = db.beginTx()

    try {
      for (vertex <- vertices) try {
        val node = tx.createNode(Label.label(vertex.label))
        node.setProperty("id", vertex.id)

        vertex match {
          case Genre(_, _, genreId, name) =>
            node.setProperty("genreId", genreId)
            node.setProperty("name", name)
          case Film(_, _, filmId, name, releaseDate) =>
            node.setProperty("filmId", filmId)
            node.setProperty("name", name)
            node.setProperty("release_date", releaseDate)
          case Director(_, _, directorId, name) =>
            node.setProperty("directorId", directorId)
            node.setProperty("name", name)
          case _ =>
            sys.error(s"Unknown $vertex.")
        }

        mapping(vertex.id) = node.getElementId
      } catch {
        case e: Exception =>
          throw new RuntimeException(s"Error in: $vertex", e)
      }

      tx.commit()
      mapping

    } finally {
      tx.close()
    }
  }

  private def populateEdges(
    db: GraphDatabaseService,
    edges: Iterable[Edge],
    vertexNodeIds: Map[VertexId, String]
  ): Long = {
    var edgeCount = 0
    val tx = db.beginTx()

    try {
      for (edge <- edges) try {
        val sourceNodeId = vertexNodeIds(edge.source)
        val sourceNode = tx.getNodeByElementId(sourceNodeId)
        if (sourceNode == null) {
          sys.error("Null source node for: " + sourceNodeId)
        }

        val destinationNodeId = vertexNodeIds(edge.destination)
        val destinationNode = tx.getNodeByElementId(destinationNodeId)
        if (destinationNode == null) {
          sys.error("Null destination node for: " + destinationNodeId)
        }

        sourceNode.createRelationshipTo(destinationNode, RelationshipType.withName(edge.label))
        edgeCount += 1

      } catch {
        case e: Exception =>
          throw new RuntimeException(s"Error in: $edge", e)
      }

      tx.commit()
      edgeCount

    } finally {
      tx.close()
    }
  }

  private def createIndices(db: GraphDatabaseService): Unit = {
    createIndex(db, "Director", "name")
    createIndex(db, "Film", "release_date")
    createIndex(db, "Film", "name")
    createIndex(db, "Genre", "name")
  }

  private def createIndex(
    db: GraphDatabaseService,
    label: String,
    property: String
  ): Unit = {
    val indexTx = db.beginTx()
    try {
      val index = indexTx.schema().indexFor(Label.label(label)).on(property).create()
      indexTx.commit()

      val queryTx = db.beginTx()
      try {
        queryTx.schema().awaitIndexOnline(index, 100, TimeUnit.SECONDS)
        queryTx.commit()

      } finally {
        queryTx.close()
      }

    } finally {
      indexTx.close()
    }
  }

  private def validate(msg: String, expected: Seq[Map[String, AnyRef]], r: Result): Int = {
    def map(r: Result) = r.asScala.map(m => m.asScala.toMap).toSeq

    def threadPrintln(s: String) = {
      println("[" + Thread.currentThread.getName + "] " + s)
    }

    val mapped_r = map(r)
    if (expected.equals(mapped_r)) {
      1
    } else {
      threadPrintln(
        "Validation failure : expected '" + expected + "', but got '" + mapped_r + "'"
      )
      0
    }
  }

  private val mutatorQueries: Seq[(String, Map[String, AnyRef], Result => Int)] = Seq(
    (
      """match (d: Director { name: $name })
        | set d.directorId = $directorId""".stripMargin,
      Map("name" -> "Jim Steel", "directorId" -> "m.03d5q13"),
      (_: Result) => 1
    ),
    (
      """match (d: Director)
        | where d.name starts with $name
        | set d.directorId = 'f1:' + d.name""".stripMargin,
      Map("name" -> "Don"),
      (_: Result) => 1
    ),
    (
      """match (f: Film)
        | where $from <= f.release_date < $to
        |  set f.rname = reverse(f.name)""".stripMargin,
      Map("from" -> "2014", "to" -> "2015"),
      (_: Result) => 1
    )
  )

  private val shortQueries: Seq[(String, Map[String, AnyRef], Result => Int)] = Seq(
    (
      "match (d: Director) where d.name = $name return d.directorId",
      Map("name" -> "Jim Steel"),
      (r: Result) => validate("Director ID: ", Seq(Map("d.directorId" -> "m.03d5q13")), r)
    ),
    (
      "match (f: Film) where f.name = $name return f.release_date",
      Map("name" -> "Hustlers #2"),
      (r: Result) => validate("Film Date: ", Seq(Map("f.release_date" -> "1996-02-01")), r)
    ),
    (
      "match (f: Film) where $from <= f.release_date < $to return count(f)",
      Map("from" -> "2014", "to" -> "2015"),
      (r: Result) => validate("Movies in 2014: ", Seq(Map("count(f)" -> Long.box(6321))), r)
    ),
    (
      "match (f: Film) where f.name starts with $name return count(f)",
      Map("name" -> "Don"),
      (r: Result) => validate("The Don movies", Seq(Map("count(f)" -> Long.box(462))), r)
    ),
    (
      """match (f: Film)-[: GENRE]->(g: Genre)
        | where f.name = $name
        | with g order by g.name
        | return collect(distinct g.name) as filmNames""".stripMargin,
      Map("name" -> "Forrest Gump"),
      (r: Result) =>
        validate(
          "The genres of \"Forrest Gump\": ",
          Seq(
            Map(
              "filmNames" -> List(
                "Comedy",
                "Comedy-drama",
                "Drama",
                "Epic film",
                "Romance Film",
                "Romantic comedy"
              ).asJava
            )
          ),
          r
        )
    )
  )

  private val longQueries: Seq[(String, Map[String, AnyRef], Result => Int)] = Seq(
    // Count the number of films.
    (
      "match (f: Film) return count(f)",
      Map(),
      (r: Result) => validate("Films", Seq(Map("count(f)" -> Long.box(233437))), r)
    ),
    // Count the number of genres.
    (
      "match (g: Genre) return count(g)",
      Map(),
      (r: Result) => validate("Genres", Seq(Map("count(g)" -> Long.box(594))), r)
    ),
    // Find how many directors directed at least 3 movies.
    (
      """match (d: Director)
        |with d, count { (d)-[: FILMS]->() } as c
        |where c > $c
        |return count(d)""".stripMargin,
      Map("c" -> Long.box(3)),
      (r: Result) =>
        validate("Directors with 3 or more movies:", Seq(Map("count(d)" -> Long.box(11619))), r)
    ),
    // Find how many genres have at least 10 directors.
    (
      """match (d: Director)-[: FILMS]->(f: Film)-[: GENRE]->(g: Genre)
        |with g, count(distinct d) as c
        |where c > $c
        |return count(g)
        |""".stripMargin,
      Map("c" -> Long.box(10)),
      (r: Result) =>
        validate("Genres with at least 10 directors:", Seq(Map("count(g)" -> Long.box(303))), r)
    ),
    // Find the genre with the most movies.
    (
      """match (g: Genre)
        |with g, count { ()-[: GENRE]->(g) } as filmCount
        |order by filmCount desc
        |limit 1
        |return g.name, filmCount""".stripMargin,
      Map(),
      (r: Result) =>
        validate(
          "Most active genre:",
          Seq(Map("g.name" -> "Drama", "filmCount" -> Long.box(70233))),
          r
        )
    ),
    // Find three directors with the most comedies.
    (
      """match (d: Director)-[: FILMS]->(f: Film)-[: GENRE]->(g: Genre)
        | where g.name = $genre
        |with d, count(f) as filmCount
        | order by filmCount desc
        | limit 1
        |return d.name, filmCount
        |""".stripMargin,
      Map("genre" -> "Comedy"),
      (r: Result) =>
        validate(
          "Funniest director: ",
          Seq(Map("d.name" -> "Charles Lamont", "filmCount" -> Long.box(194))),
          r
        )
    ),
    // Find the number of directors that filmed a movie that had two directors
    // between 1985 and 2010.
    (
      """match (d1: Director)-[: FILMS]->(film: Film)<-[: FILMS]-(d2: Director)
        |  where $from < film.release_date < $to
        |return count(distinct d1) as directors""".stripMargin,
      Map("from" -> "1985", "to" -> "2010"),
      (r: Result) =>
        validate(
          "Had at least one 2-director movie in 1985-2010: ",
          Seq(Map("directors" -> Long.box(11209))),
          r
        )
    ),
    // Find the number of 3-cliques of directors, in which directors are adjacent
    // if they made a movie together after 2005.
    (
      """match (d1x: Director)-[: FILMS]->(film1: Film)<-[: FILMS]-(d1y: Director),
        |  (d2x: Director)-[: FILMS]->(film2: Film)<-[: FILMS]-(d2y: Director),
        |  (d3x: Director)-[: FILMS]->(film3: Film)<-[: FILMS]-(d3y: Director)
        |where d1x <> d1y and d2x <> d2y and d3x <> d3y
        |  and d1x = d2x and d1y = d3x and d2y = d3y
        |  and film1 <> film2 and film1 <> film3 and film2 <> film3
        |  and film1.release_date > $from
        |  and film2.release_date > $from
        |  and film3.release_date > $from
        |return count(distinct [d1x, d1y, d2y]) as cliques""".stripMargin,
      Map("from" -> "2005"),
      (r: Result) => validate("Director 3-cliques: ", Seq(Map("cliques" -> Long.box(1008))), r)
    )
  )

  // Workload in terms of threads and query types.
  private val queryWorkload = Seq(
    (longQueryThreads, longQueries, longQueryRepeats, (i: Int) => 3 * i),
    (shortQueryThreads, shortQueries, shortQueryRepeats, (i: Int) => i),
    (mutatorQueryThreads, mutatorQueries, mutatorQueryRepeats, (i: Int) => i)
  )

  /**
   * Calculates the total number of queries to be performed.
   */
  def totalQueryCount(): Int = {
    queryWorkload
      .map(t => {
        val (count, queries, repeats, _) = t
        count * queries.length * repeats
      })
      .sum
  }

  private class QueriesThread extends Thread {
    var numQueries = 0
  }

  /**
   * Runs the benchmark.
   */
  def run(): Int = {
    // Create different threads for different query types.
    val queryThreads = queryWorkload.flatMap(t => {
      val (count, queries, repeats, offset) = t
      for (threadIndex <- 0 until count) yield new QueriesThread {
        override def run(): Unit = {
          numQueries += runQueries(graphDb, queries, repeats, offset(threadIndex))
        }
      }
    })

    // Start query threads and wait until they finish.
    queryThreads.foreach(_.start())
    queryThreads.foreach(_.join())

    // Sum the number of successful queries across all threads.
    queryThreads.map(_.numQueries).sum
  }

  private def runQueries(
    db: GraphDatabaseService,
    queries: Seq[(String, Map[String, AnyRef], Result => Int)],
    repeats: Int,
    offset: Int
  ): Int = {
    var numSuccessfulQueries = 0
    for (_ <- 0 until repeats) {
      for ((query, params, action) <- rotate(queries, offset)) {
        numSuccessfulQueries += runQuery(db, query, params, action)
      }
    }
    numSuccessfulQueries
  }

  private def rotate[T](s: Seq[T], n: Int): Seq[T] =
    s.drop(n % s.length) ++ s.take(n % s.length)

  private def runQuery(
    db: GraphDatabaseService,
    query: String,
    params: Map[String, AnyRef],
    f: Result => Int
  ): Int = {
    var numSuccessfulQueries = 0

    val tx = db.beginTx()
    try {
      val result = tx.execute(query, params.asJava)
      numSuccessfulQueries += f(result)
      tx.commit()
    } finally {
      tx.close()
    }

    numSuccessfulQueries
  }
}
