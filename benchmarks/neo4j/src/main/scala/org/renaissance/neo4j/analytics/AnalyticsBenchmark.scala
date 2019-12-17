package org.renaissance.neo4j.analytics

import java.io.File
import java.nio.charset.StandardCharsets
import java.util
import java.util.concurrent.TimeUnit
import java.util.function.Consumer

import net.liftweb.json._
import org.apache.commons.io.FileUtils
import org.apache.commons.io.IOUtils
import org.neo4j.graphdb.GraphDatabaseService
import org.neo4j.graphdb.Label
import org.neo4j.graphdb.RelationshipType
import org.neo4j.graphdb.Result
import org.neo4j.graphdb.factory.{GraphDatabaseFactory, GraphDatabaseSettings}
import org.renaissance.BenchmarkResult.Assert

import scala.collection._
import scala.collection.JavaConverters._

class AnalyticsBenchmark(
  val graphDir: File,
  val longQueryCount: Option[Int],
  val shortQueryCount: Option[Int],
  val mutatorQueryCount: Option[Int]
) {
  private var db: GraphDatabaseService = _

  private val CPU_COUNT = Runtime.getRuntime.availableProcessors

  private val LONG_QUERY_NUM = longQueryCount.getOrElse(2)

  private val SHORT_QUERY_NUM = shortQueryCount.getOrElse(1)

  private val MUTATOR_QUERY_NUM = mutatorQueryCount.getOrElse(1)

  implicit def val2Label(v : String) : Label = Label.label(v.toString)
  implicit def val2Type(v : String) : RelationshipType = RelationshipType.withName(v.toString)

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
    db = new GraphDatabaseFactory()
      .newEmbeddedDatabaseBuilder(graphDir)
      .setConfig(GraphDatabaseSettings.pagecache_memory,"500M")
      .newGraphDatabase()
    Runtime.getRuntime.addShutdownHook(new Thread {
      override def run(): Unit = {
        db.shutdown()
        FileUtils.deleteDirectory(graphDir)
      }
    })

    val mapping = populateVertices(db)
    populateEdges(db, mapping)
    createIndices(db)
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
            val node = db.createNode(label)
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
            val node = db.createNode(label)
            node.setProperty("id", (vertex \ "id").extract[Int])
            node.setProperty("filmId", (vertex \ "filmId").extract[String])
            node.setProperty("name", filmName)
            node.setProperty("release_date", (vertex \ "release_date").extract[String])
            node
          case "Director" =>
            val node = db.createNode(label)
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
        sourceNode.createRelationshipTo(destinationNode, label)
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
    createIndex(db, "Director", "name")
    createIndex(db, "Film", "release_date")
    createIndex(db, "Film", "name")
    createIndex(db, "Genre", "name")
  }

  private def createIndex(
    db: GraphDatabaseService,
    label: Label,
    property: String
  ): Unit = {
    var tx = db.beginTx()
    val schema = db.schema()
    val index = schema
      .indexFor(label)
      .on(property)
      .create()
    tx.success()
    tx.close()

    tx = db.beginTx()
    db.schema().awaitIndexOnline(index, 1000, TimeUnit.SECONDS)
    tx.success()
    tx.close()
  }

  private def flush(r: Result) = map(r).mkString("\n")

  private def map(r: Result) = r.asScala.map(m => m.asScala.toMap).toSeq

  private def validate(msg:String, expected: Seq[Map[String,AnyRef]], r:Result) = {
    Assert.assertEquals(expected, map(r), msg)
  }

  private def silentPrintln(s: String) = {}

  private def threadPrintln(s: String) = {
    println("[" + Thread.currentThread.getName + "] " + s)
  }

  private val mutatorQueries = Seq(
    (
      """match (d: Director { name: $name })
        | set d.directorId = $directorId""".stripMargin,
        Map("name" -> "Jim Steel", "directorId" -> "m.03d5q13"),
      (r: Result) => threadPrintln("Done.")
    ),
    (
      """match (d: Director)
        | where d.name starts with $name
        | set d.directorId = 'f1:' + d.name""".stripMargin,
      Map("name"->"Don"),
      (r: Result) => threadPrintln("Done.")
    ),
    (
      """match (f: Film)
        | where $from <= f.release_date < $to
        |  set f.rname = reverse(f.name)""".stripMargin,
      Map("from"->"2014","to"->"2015"),
      (r: Result) => threadPrintln("Done.")
    )
  )

  private val shortQueries = Seq(
    (
      "match (d: Director) where d.name = $name return d.directorId",
      Map("name"->"Jim Steel"),
      (r: Result) => validate("Director ID: ", Seq(Map("d.directorId" -> "m.03d5q13")), r)
    ),
    (
      "match (f: Film) where f.name = $name return f.release_date",
      Map("name"->"Hustlers #2"),
      (r: Result) => validate("Film Date: ", Seq(Map("f.release_date" -> "1996-02-01")), r)
    ),
    (
      "match (f: Film) where $from <= f.release_date < $to return count(f)",
        Map("from"->"2014","to"->"2015"),
      (r: Result) => validate("Movies in 2014: ", Seq(Map("count(f)" -> Long.box(6321))), r)
    ),
    (
      "match (f: Film) where f.name starts with $name return count(f)",
      Map("name"->"Don"),
      (r: Result) => validate("The Don movies", Seq(Map("count(f)"->Long.box(462))), r)
    ),
    (
      """match (f: Film)-[: GENRE]->(g: Genre)
        | where f.name = $name
        | with g order by g.name
        | return collect(distinct g.name) as filmNames""".stripMargin,
        Map("name"->"Forrest Gump"),
      (r: Result) => validate("The genres of \"Forrest Gump\": ",
        Seq(Map("filmNames"->List("Comedy", "Comedy-drama", "Drama", "Epic film", "Romance Film", "Romantic comedy").asJava)), r)
    )
  )

  private val longQueries: Seq[Tuple3[String,Map[String,AnyRef],(Result)=>Unit]] = Seq(
    // Count the number of films.
    (
      "match (f: Film) return count(f)",
      Map(),
      (r: Result) => validate("Films", Seq(Map("count(f)"->Long.box(233437))), r)
    ),
    // Count the number of genres.
    (
      "match (g: Genre) return count(g)",
      Map(),
      (r: Result) => validate("Genres", Seq(Map("count(g)"->Long.box(594))), r)
    ),
    // Find how many directors directed at least 3 movies.
    (
      """match (d: Director)
        |with d, size((d)-[: FILMS]->()) as c
        |where c > $c
        |return count(d)""".stripMargin,
      Map("c"->Long.box(3)),
      (r: Result) => validate("Directors with 3 or more movies:", Seq(Map("count(d)"->Long.box(11619))), r)
    ),
    // Find how many genres have at least 10 directors.
    (
      """match (d: Director)-[: FILMS]->(f: Film)-[: GENRE]->(g: Genre)
        |with g, count(distinct d) as c
        |where c > $c
        |return count(g)
        |""".stripMargin,
      Map("c"->Long.box(10)),
      (r: Result) => validate("Genres with at least 10 directors:", Seq(Map("count(g)"->Long.box(303))), r)
    ),
    // Find the genre with the most movies.
    (
      """match (g: Genre)
        |with g, size(()-[: GENRE]->(g)) as filmCount
        |order by filmCount desc
        |limit 1
        |return g.name, filmCount""".stripMargin,
    Map(),
      (r: Result) => validate("Most active genre:", Seq(Map("g.name"->"Drama","filmCount"->Long.box(70233))), r)
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
      Map("genre"->"Comedy"),
      (r: Result) => validate("Funniest director: ", Seq(Map("d.name"->"Charles Lamont","filmCount"->Long.box(194))), r)
    ),
    // Find the number of directors that filmed a movie that had two directors
    // between 1985 and 2010.
    (
      """match (d1: Director)-[: FILMS]->(film: Film)<-[: FILMS]-(d2: Director)
        |  where $from < film.release_date < $to
        |return count(distinct d1) as directors""".stripMargin,
      Map("from"->"1985","to"->"2010"),
      (r: Result) => validate("Had at least one 2-director movie in 1985-2010: ", Seq(Map("directors"->Long.box(11209))), r)

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
      Map("from"->"2005"),
      (r: Result) => validate("Director 3-cliques: ", Seq(Map("cliques"->Long.box(1008))), r)
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
    queries: Seq[(String, Map[String,AnyRef], Result => Unit)],
    repeats: Int,
    offset: Int
  ): Unit = {
    for (i <- 0 until repeats) {
      for ((query, params, action) <- rotate(queries, offset)) {
        runQuery(db, query, params, action)
      }
    }
  }

  private def runQuery(db: GraphDatabaseService, query: String, params: Map[String,AnyRef],f: Result => Unit): Unit = {
    val tx = db.beginTx()
    try {
      val result = db.execute(query,params.asJava)
      f(result)
      tx.success()
    } finally {
      tx.close()
    }
  }
}
