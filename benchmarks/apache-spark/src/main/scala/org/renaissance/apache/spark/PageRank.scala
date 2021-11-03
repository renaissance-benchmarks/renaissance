package org.renaissance.apache.spark

import org.apache.spark.rdd.RDD
import org.renaissance.Benchmark
import org.renaissance.Benchmark._
import org.renaissance.BenchmarkContext
import org.renaissance.BenchmarkResult
import org.renaissance.BenchmarkResult.Assert
import org.renaissance.BenchmarkResult.Validators
import org.renaissance.License
import org.renaissance.apache.spark.ResourceUtil.sourceFromZipResource

import java.nio.file.Files
import java.nio.file.Path
import java.util.regex.Pattern
import scala.io.BufferedSource

@Name("page-rank")
@Group("apache-spark")
@Summary("Runs a number of PageRank iterations, using RDDs.")
@Licenses(Array(License.APACHE2))
@Repetitions(20)
@Parameter(
  name = "spark_thread_limit",
  defaultValue = "12",
  summary = "Maximum number of threads for the Spark local executor."
)
@Parameter(
  name = "max_iterations",
  defaultValue = "2",
  summary = "Maximum number of iterations of the page rank algorithm."
)
@Parameter(
  name = "input_line_count",
  defaultValue = "-1",
  summary = "Number of lines to take as input from the input dataset."
)
@Parameter(name = "expected_rank_count", defaultValue = "598652")
@Parameter(name = "expected_rank_hash", defaultValue = "9b39ddf5eaa8b3d2")
@Configuration(
  name = "test",
  settings = Array(
    "input_line_count = 5000",
    "expected_rank_count = 1664",
    "expected_rank_hash = 797021674f62a217"
  )
)
@Configuration(name = "jmh")
final class PageRank extends Benchmark with SparkUtil {

  // TODO: Consolidate benchmark parameters across the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/27

  /**
   * Maximum difference in neighboring ranks for web sites in the same class.
   * The value is slightly lower but in the same order as 1/685230, which
   * corresponds to the number of web sites in the input data set.
   */
  private val rankDifferenceLimit = 1e-6

  private val inputZipResource = "/web-berkstan.txt.zip"

  private val inputZipEntry = "web-BerkStan.txt"

  private var maxIterationsParam: Int = _

  private var expectedRankCountParam: Int = _

  private var expectedRankHashParam: String = _

  private var inputLinks: RDD[(Int, Iterable[Int])] = _

  private def copyLinesToFile(
    source: BufferedSource,
    lineCount: Int,
    outputFile: Path
  ): Path = {
    import scala.jdk.CollectionConverters._

    try {
      var lines = source.getLines().dropWhile(_.startsWith("#"))
      if (lineCount >= 0) {
        lines = lines.take(lineCount)
      }

      // Write output using UTF-8 encoding.
      Files.write(outputFile, lines.toSeq.asJava)
    } finally {
      source.close()
    }
  }

  private def loadData(inputFile: Path) = {
    val splitter = Pattern.compile("\\s+")
    sparkContext
      .textFile(inputFile.toString)
      .map { line =>
        val parts = splitter.split(line, 2)
        parts(0).toInt -> parts(1).toInt
      }
      .groupByKey()
  }

  override def setUpBeforeAll(bc: BenchmarkContext): Unit = {
    setUpSparkContext(bc)

    maxIterationsParam = bc.parameter("max_iterations").toPositiveInteger
    expectedRankCountParam = bc.parameter("expected_rank_count").toInteger
    expectedRankHashParam = bc.parameter("expected_rank_hash").value

    val inputFile = copyLinesToFile(
      sourceFromZipResource(inputZipResource, inputZipEntry),
      bc.parameter("input_line_count").toInteger,
      bc.scratchDirectory().resolve("websites.txt")
    )

    inputLinks = ensureCached(loadData(inputFile))
  }

  override def run(bc: BenchmarkContext): BenchmarkResult = {
    var ranks = inputLinks.mapValues(_ => 1.0)
    for (_ <- 0 until maxIterationsParam) {
      val contributions = inputLinks.join(ranks).values.flatMap {
        case (urls, rank) => urls.map(url => (url, rank / urls.size))
      }
      ranks = contributions.reduceByKey(_ + _).mapValues(0.15 + 0.85 * _)
    }

    //
    // Trigger the computation by counting the ranks. An alternative is to
    // call collect(), which would also gather all the data into the driver
    // as part of the measured operation. A typical application would probably
    // iterate over a (potentially large) result (which is what count() may
    // do) instead of collecting it into one place.
    //
    val rankCount: Int = ranks.count().toInt

    new BenchmarkResult {
      //
      // Check the number of ranks and the string representation of the web site
      // identifiers ordered by rank and web site id (for equivalent ranks). To
      // work around numerical instability issues, the sites are first pre-sorted
      // by rank, and the ordering is then relaxed so that neighboring ranks that
      // differ only slightly are considered equal.
      //
      override def validate(): Unit = {
        import scala.jdk.CollectionConverters._

        Assert.assertEquals(expectedRankCountParam, rankCount, "ranks count")

        val preSortedEntries = ranks.sortBy { case (_, rank) => rank }.collect()
        val sortedEntries = relaxedRanks(preSortedEntries, rankDifferenceLimit).sortBy {
          case (url, rank) => (rank, url)
        }

        val rankLines = sortedEntries.map { case (url, _) => url.toString }.toList
        Validators.hashing(expectedRankHashParam, rankLines.asJava).validate()
      }

      private def relaxedRanks(entries: Array[(Int, Double)], diffLimit: Double) = {
        var prevRank = entries.head._2
        var groupRank = prevRank

        entries
          .map {
            case (url, rank) =>
              val diff = rank - prevRank
              if (diff > diffLimit) {
                groupRank = rank
              }

              prevRank = rank
              (url, groupRank)
          }
      }

    }
  }

  override def tearDownAfterAll(bc: BenchmarkContext): Unit = {
    tearDownSparkContext()
  }
}
