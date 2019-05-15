package org.renaissance.neo4j.analytics

import java.io.File
import java.nio.charset.StandardCharsets
import java.util
import java.util.function.Consumer

import net.liftweb.json._
import org.apache.commons.io.FileUtils
import org.apache.commons.io.IOUtils
import org.neo4j.graphdb.GraphDatabaseService
import org.neo4j.graphdb.Label
import org.neo4j.graphdb.RelationshipType
import org.neo4j.graphdb.Result
import org.neo4j.graphdb.factory.GraphDatabaseFactory

import scala.collection._

class AnalyticsBenchmark(
  val graphDir: File,
  val longQueryCount: Option[Int],
  val shortQueryCount: Option[Int],
  val mutatorQueryCount: Option[Int]
) {
  private var db: GraphDatabaseService = null

  private val CPU_COUNT = Runtime.getRuntime.availableProcessors

  private val LONG_QUERY_NUM = longQueryCount.getOrElse(2)

  private val SHORT_QUERY_NUM = shortQueryCount.getOrElse(1)

  private val MUTATOR_QUERY_NUM = mutatorQueryCount.getOrElse(1)

  private val GENRE = new RelationshipType {
    override def name(): String = "GENRE"
  }

  private val FILMS = new RelationshipType {
    override def name(): String = "FILMS"
  }

  private val relationshipTypes = Map(
    "GENRE" -> GENRE,
    "FILMS" -> FILMS
  )

  private val directorLabel = new Label {
    override def name(): String = "Director"
  }

  private val filmLabel = new Label {
    override def name(): String = "Film"
  }

  private val genreLabel = new Label {
    override def name(): String = "Genre"
  }

  /** Must be called before calling `run`.
   */
  def setupAll(): Unit = {
    // TODO: Unify how the scratch directories are handled throughout the suite.
    //  See: https://github.com/D-iii-S/renaissance-benchmarks/issues/13
    println("Checking previous DB remnants in " + graphDir.getAbsoluteFile)
    if (graphDir.exists) {
      println("DB remnants detected, deleting ...")
      FileUtils.forceDelete(graphDir)
    }
    db = new GraphDatabaseFactory().newEmbeddedDatabase(graphDir)
    Runtime.getRuntime.addShutdownHook(new Thread {
      override def run() = {
        db.shutdown()
        FileUtils.deleteDirectory(graphDir)
      }
    })

    createIndices(db)
    val mapping = populateVertices(db)
    populateEdges(db, mapping)
    println("Graph database created.")
  }

  /** Runs the benchmark.
   */
  def run(): Unit = {
    val longThreads = startLongQueryThreads(db)
    val shortThreads = startShortQueryThreads(db)
    val mutatorThreads = startMutatorQueryThreads(db)
    longThreads.foreach(_.join())
    shortThreads.foreach(_.join())
    mutatorThreads.foreach(_.join())
  }

  /** Must be called after calling `run`.
   */
  def tearAll(): Unit = {
    db.shutdown()
  }

  private def populateVertices(db: GraphDatabaseService): Map[Integer, Long] = {
    println("Populating vertices...")
    val mapping = mutable.Map[Integer, Long]()
    val tx = db.beginTx()
    try {
      val rawVertices =
        IOUtils.toString(getClass.getResourceAsStream("/vertices.json"), StandardCharsets.UTF_8)
      val vertices = parse(rawVertices)
      implicit val formats = DefaultFormats
      for (field <- vertices.asInstanceOf[JObject].obj) try {
        val id = field.name.toInt
        val vertex = field.value
        val label = (vertex \ "label").extract[String]
        val node = label match {
          case "Genre" =>
            val node = db.createNode(genreLabel)
            node.setProperty("id", (vertex \ "id").extract[Int])
            node.setProperty("genreId", (vertex \ "genreId").extract[String])
            node.setProperty("name", (vertex \ "name").extract[String])
            node
          case "Film" =>
            val filmName = if ((vertex \ "name").toOpt.get.isInstanceOf[JBool]) {
              (vertex \ "name").extract[Boolean].toString
            } else {
              (vertex \ "name").extract[String]
            }
            val node = db.createNode(filmLabel)
            node.setProperty("id", (vertex \ "id").extract[Int])
            node.setProperty("filmId", (vertex \ "filmId").extract[String])
            node.setProperty("name", filmName)
            node.setProperty("release_date", (vertex \ "release_date").extract[String])
            node
          case "Director" =>
            val node = db.createNode(directorLabel)
            node.setProperty("id", (vertex \ "id").extract[Int])
            node.setProperty("directorId", (vertex \ "directorId").extract[String])
            node.setProperty("name", (vertex \ "name").extract[String])
            node
          case _ =>
            sys.error(s"Unknown $field.")
        }
        mapping(id) = node.getId
      } catch {
        case e: Exception =>
          throw new RuntimeException("Error in: " + field, e)
      }
      mapping
    } finally {
      tx.success()
      tx.close()
    }
  }

  private def populateEdges(db: GraphDatabaseService, mapping: Map[Integer, Long]): Unit = {
    println("Populating edges...")
    val tx = db.beginTx()
    try {
      val rawEdges =
        IOUtils.toString(getClass.getResourceAsStream("/edges.json"), StandardCharsets.UTF_8)
      val vertices = parse(rawEdges)
      implicit val formats = DefaultFormats
      for (field <- vertices.asInstanceOf[JObject].obj) try {
        val name = field.name
        val vertex = field.value
        val source = mapping((vertex \ "source").extract[Int])
        val destination = mapping((vertex \ "destination").extract[Int])
        val label = (vertex \ "label").extract[String]
        val sourceNode = db.getNodeById(source)
        if (sourceNode == null) {
          sys.error("Null source node for: " + source)
        }
        val destinationNode = db.getNodeById(destination)
        if (destinationNode == null) {
          sys.error("Null destination node for: " + destination)
        }
        val relationship =
          sourceNode.createRelationshipTo(destinationNode, relationshipTypes(label))
      } catch {
        case e: Exception =>
          throw new RuntimeException("Error in: " + field, e)
      }
    } finally {
      tx.success()
      tx.close()
    }
  }

  private def createIndices(db: GraphDatabaseService): Unit = {
    println("Creating indices...")
    createIndex(db, directorLabel, "id")
    createIndex(db, directorLabel, "name")
    createIndex(db, filmLabel, "release_date")
    createIndex(db, filmLabel, "name")
  }

  private def createIndex(
    db: GraphDatabaseService,
    label: Label,
    property: String
  ): Unit = {
    val tx = db.beginTx()
    val schema = db.schema()
    schema
      .indexFor(label)
      .on(property)
      .create()
    tx.success()
    tx.close()
  }

  private def flush(r: Result): String = {
    val buffer = mutable.Buffer[String]()
    r.stream()
      .forEach(new Consumer[util.Map[String, AnyRef]] {
        override def accept(t: util.Map[String, AnyRef]): Unit = {
          buffer += t.toString
        }
      })
    buffer.mkString("\n")
  }

  private def threadPrintln(s: String) = {
    println("[" + Thread.currentThread.getName + "] " + s)
  }

  private val mutatorQueries = Seq(
    (
      "match (d: Director { name: 'Jim Steel' })" +
        "set d.directorId = 'm.03d5q13'",
      (r: Result) => threadPrintln("Done.")
    ),
    (
      "match (d: Director) where d.name starts with 'Don' " +
        "set d.directorId = 'f1:' + d.name",
      (r: Result) => threadPrintln("Done.")
    ),
    (
      "match (f: Film) " +
        "where f.release_date >= '2014' and f.release_date < '2015' " +
        "set f.name = reverse(f.name)",
      (r: Result) => threadPrintln("Done.")
    )
  )

  private def silentPrintln(s: String) = {}

  private val shortQueries = Seq(
    (
      "match (d: Director) where d.name = 'Jim Steel' return d.directorId",
      (r: Result) => silentPrintln("Director ID: " + flush(r))
    ),
    (
      "match (f: Film) where f.name = 'Hustlers' return f.release_date",
      (r: Result) => silentPrintln("Release date: " + flush(r))
    ),
    (
      "match (f: Film) where f.release_date >= '2014' and f.release_date < '2015' " +
        "return count(f)",
      (r: Result) => silentPrintln("Movies in 2014: " + flush(r))
    ),
    (
      "match (f: Film) where f.name starts with 'Don' " +
        "return count(f)",
      (r: Result) => silentPrintln("The Don movies: " + flush(r))
    ),
    (
      "match (f: Film)-[: GENRE]->(g: Genre) where f.name = 'The Journey' " +
        "return collect(distinct g.name)",
      (r: Result) => silentPrintln("The genres of The Journey: " + flush(r))
    )
  )

  private val longQueries = Seq(
    // Count the number of films.
    (
      "match (f: Film) return count(f)",
      (r: Result) => threadPrintln("Films: " + flush(r))
    ),
    // Count the number of genres.
    (
      "match (g: Genre) return count(g)",
      (r: Result) => threadPrintln("Genres: " + flush(r))
    ),
    // Find how many directors directed at least 3 movies.
    (
      "match (d: Director)-[: FILMS]->(f: Film) " +
        "with d, count(f) as c " +
        "where c > 3 " +
        "return count(d)",
      (r: Result) => threadPrintln("Directors with 3 or more movies: " + flush(r))
    ),
    // Find how many genres have at least 10 directors.
    (
      "match (d: Director)-[: FILMS]->(f: Film)-[: GENRE]->(g: Genre) " +
        "with g, count(distinct d) as c " +
        "where c > 10 " +
        "return count(g)",
      (r: Result) => threadPrintln("Genres with at least 10 directors: " + flush(r))
    ),
    // Find the genre with the most movies.
    (
      "match (f: Film)-[: GENRE]->(g: Genre) " +
        "with g, count(f) as filmCount " +
        "order by filmCount desc " +
        "limit 1 " +
        "return g.name, filmCount",
      (r: Result) => threadPrintln("Most active genre: " + flush(r))
    ),
    // Find three directors with the most comedies.
    (
      "match (d: Director)-[: FILMS]->(f: Film)-[: GENRE]->(g: Genre) " +
        "where g.name = 'Comedy' " +
        "with d, count(f) as filmCount " +
        "order by filmCount desc " +
        "limit 1 " +
        "return d.name, filmCount",
      (r: Result) => threadPrintln("Funniest director: " + flush(r))
    ),
    // Find the number of directors that filmed a movie that had two directors
    // between 1985 and 2010.
    (
      "match (d1: Director)-[: FILMS]->(film: Film)<-[: FILMS]-(d2: Director) " +
        "where d1 <> d2 and film.release_date > '1985' " +
        "  and film.release_date < '2010' " +
        "with distinct d1 as director " +
        "return count(director)",
      (r: Result) => {
        threadPrintln("Had at least one 2-director movie in 1985-2010: " + flush(r))
      }
    ),
    // Find the number of 3-cliques of directors, in which directors are adjacent
    // if they made a movie together after 2005.
    (
      "match (d1x: Director)-[: FILMS]->(film1: Film)<-[: FILMS]-(d1y: Director), " +
        "  (d2x: Director)-[: FILMS]->(film2: Film)<-[: FILMS]-(d2y: Director), " +
        "  (d3x: Director)-[: FILMS]->(film3: Film)<-[: FILMS]-(d3y: Director) " +
        "where d1x <> d1y and d2x <> d2y and d3x <> d3y " +
        "  and d1x = d2x and d1y = d3x and d2y = d3y " +
        "  and film1 <> film2 and film1 <> film3 and film2 <> film3 " +
        "  and film1.release_date > '2005' " +
        "  and film2.release_date > '2005' " +
        "  and film3.release_date > '2005' " +
        "with distinct [d1x.name, d1y.name, d2y.name] as clique " +
        "return count(clique)",
      (r: Result) => threadPrintln("Director 3-cliques: " + flush(r))
    )
  )

  private def rotate[T](s: Seq[T], n: Int): Seq[T] =
    s.drop(n % s.length) ++ s.take(n % s.length)

  private def startMutatorQueryThreads(db: GraphDatabaseService): Seq[Thread] = {
    val mutatorCount = math.max(1, MUTATOR_QUERY_NUM)
    val threads = for (p <- 0 until mutatorCount)
      yield
        new Thread {
          override def run(): Unit = {
            runQueries(db, mutatorQueries, 12, p)
          }
        }
    threads.foreach(_.start())
    threads
  }

  private def startShortQueryThreads(db: GraphDatabaseService): Seq[Thread] = {
    val shortCount = math.max(1, SHORT_QUERY_NUM)
    val threads = for (p <- 0 until shortCount)
      yield
        new Thread {
          override def run(): Unit = {
            runQueries(db, shortQueries, 150, p)
          }
        }
    threads.foreach(_.start())
    threads
  }

  private def startLongQueryThreads(db: GraphDatabaseService): Seq[Thread] = {
    val longCount = math.max(1, LONG_QUERY_NUM)
    val threads = for (p <- 0 until longCount)
      yield
        new Thread {
          override def run(): Unit = {
            runQueries(db, longQueries, 1, 3 * p)
          }
        }
    threads.foreach(_.start())
    threads
  }

  private def runQueries(
    db: GraphDatabaseService,
    queries: Seq[(String, Result => Unit)],
    repeats: Int,
    offset: Int
  ): Unit = {
    for (i <- 0 until repeats) {
      for ((query, action) <- rotate(queries, offset)) {
        runQuery(db, query, action)
      }
    }
  }

  private def runQuery(db: GraphDatabaseService, query: String, f: Result => Unit): Unit = {
    val tx = db.beginTx()
    try {
      val result = db.execute(query)
      f(result)
      tx.success()
    } finally {
      tx.close()
    }
  }
}
