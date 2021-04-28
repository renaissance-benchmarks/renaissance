package org.renaissance.apache.spark

import java.util.regex.Pattern

import org.apache.spark.SparkContext
import org.apache.spark.rdd.RDD
import org.renaissance.Benchmark
import org.renaissance.Benchmark._
import org.renaissance.BenchmarkContext
import org.renaissance.BenchmarkResult
import org.renaissance.BenchmarkResult.Assert
import org.renaissance.BenchmarkResult.Validators
import org.renaissance.License

import scala.collection.JavaConverters._

@Name("page-rank")
@Group("apache-spark")
@Summary("Runs a number of PageRank iterations, using RDDs.")
@Licenses(Array(License.APACHE2))
@Repetitions(20)
@Parameter(
  name = "spark_executor_count",
  defaultValue = "4",
  summary = "Number of executor instances."
)
@Parameter(
  name = "spark_executor_thread_count",
  defaultValue = "$cpu.count",
  summary = "Number of threads per executor."
)
@Parameter(name = "input_line_count", defaultValue = "-1")
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

  private var inputLineCountParam: Int = _

  private var expectedRankCountParam: Int = _

  private var expectedRankHashParam: String = _

  /** Number of iterations of the page rank algorithm. */
  private val PAGE_RANK_ITERATIONS = 2

  private val INPUT_ZIP_RESOURCE = "/web-berkstan.txt.zip"

  private val INPUT_ZIP_ENTRY = "web-BerkStan.txt"

  /**
   * Maximum difference in neighboring ranks for web sites in the same class.
   * The value is slightly lower but in the same order as 1/685230, which
   * corresponds to the number of web sites in the input data set
   */
  private val RANK_DIFFERENCE_LIMIT = 1e-6

  private var sc: SparkContext = _

  private var links: RDD[(Int, Iterable[Int])] = _

  private def loadData(zipName: String, entryName: String, lineCount: Int) = {
    val inputSource = ZipResourceUtil.sourceFromZipResource(entryName, zipName)

    try {
      var inputLines = inputSource.getLines().dropWhile(_.startsWith("#"))
      if (lineCount >= 0) {
        inputLines = inputLines.take(lineCount)
      }

      val splitter = Pattern.compile("\\s+")
      sc.parallelize(inputLines.toSeq)
        .map { line =>
          val parts = splitter.split(line, 2)
          parts(0).toInt -> parts(1).toInt
        }
        .groupByKey()
        .cache()
    } finally {
      inputSource.close()
    }
  }

  override def setUpBeforeAll(bc: BenchmarkContext): Unit = {
    inputLineCountParam = bc.parameter("input_line_count").toInteger
    expectedRankCountParam = bc.parameter("expected_rank_count").toInteger
    expectedRankHashParam = bc.parameter("expected_rank_hash").value

    sc = setUpSparkContext(bc)
    links = loadData(INPUT_ZIP_RESOURCE, INPUT_ZIP_ENTRY, inputLineCountParam)
    ensureCaching(links)
  }

  override def run(bc: BenchmarkContext): BenchmarkResult = {
    var ranks = links.mapValues(_ => 1.0)
    for (_ <- 0 until PAGE_RANK_ITERATIONS) {
      val contributions = links.join(ranks).values.flatMap {
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
      override def validate() = {
        Assert.assertEquals(expectedRankCountParam, rankCount, "ranks count")

        val preSortedEntries = ranks.sortBy { case (_, rank) => rank }.collect
        val sortedEntries = relaxedRanks(preSortedEntries, RANK_DIFFERENCE_LIMIT).sortBy {
          case (url, rank) => (rank, url)
        }

        val rankLines = sortedEntries.map { case (url, _) => url.toString }.toList
        Validators.hashing(expectedRankHashParam, rankLines.asJava).validate()
      }

      private def relaxedRanks(entries: Seq[(Int, Double)], diffLimit: Double) = {
        var prevRank = entries(0)._2
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
    tearDownSparkContext(sc)
  }
}
