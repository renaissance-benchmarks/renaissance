package org.renaissance.apache.spark

import java.nio.file.Path
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
// Work around @Repeatable annotations not working in this Scala version.
@Parameters(
  Array(
    new Parameter(name = "thread_count", defaultValue = "$cpu.count"),
    new Parameter(name = "input_line_count", defaultValue = "-1"),
    new Parameter(name = "expected_rank_count", defaultValue = "598652"),
    new Parameter(name = "expected_rank_hash", defaultValue = "d8bf7171feef1b87")
  )
)
@Configurations(
  Array(
    new Configuration(
      name = "test",
      settings = Array(
        "input_line_count = 5000",
        "expected_rank_count = 1661",
        "expected_rank_hash=7ca80582125b8ca7"
      )
    ),
    new Configuration(name = "jmh")
  )
)
final class PageRank extends Benchmark with SparkUtil {

  // TODO: Consolidate benchmark parameters across the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/27

  private var threadCountParam: Int = _

  private var inputLineCountParam: Int = _

  private var expectedRankCountParam: Int = _

  private var expectedRankHashParam: String = _

  private val ITERATIONS = 2

  // TODO: Unify handling of scratch directories throughout the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/13

  val inputZipFile = "web-berkstan.txt.zip"
  val inputFile = "web-BerkStan.txt"

  var sc: SparkContext = _

  var links: RDD[(String, Iterable[String])] = _

  var tempDirPath: Path = _

  def loadData(
    zipName: String,
    entryName: String,
    lineCount: Int
  ): RDD[(String, Iterable[String])] = {
    val inputSource = ZipResourceUtil.sourceFromZipResource(entryName, zipName)
    try {
      var inputLines = inputSource.getLines()
      if (lineCount >= 0) {
        inputLines = inputLines.take(lineCount)
      }

      val splitter = Pattern.compile("\\s+")
      sc.parallelize(inputLines.toSeq)
        .map { line =>
          val parts = splitter.split(line)
          parts(0) -> parts(1)
        }
        .distinct()
        .groupByKey()
        .cache()
    } finally {
      inputSource.close()
    }
  }

  override def setUpBeforeAll(c: BenchmarkContext): Unit = {
    threadCountParam = c.intParameter("thread_count")
    inputLineCountParam = c.intParameter("input_line_count")
    expectedRankCountParam = c.intParameter("expected_rank_count")
    expectedRankHashParam = c.stringParameter("expected_rank_hash")

    tempDirPath = c.generateTempDir("page_rank")
    sc = setUpSparkContext(tempDirPath, threadCountParam, "page-rank")
    links = loadData(inputZipFile, inputFile, inputLineCountParam)
  }

  override def run(c: BenchmarkContext): BenchmarkResult = {
    var ranks = links.mapValues(_ => 1.0)

    for (_ <- 0 until ITERATIONS) {
      val contributions = links.join(ranks).values.flatMap {
        case (urls, rank) =>
          urls.map(url => (url, rank / urls.size))
      }
      ranks = contributions.reduceByKey(_ + _).mapValues(0.15 + 0.85 * _)
    }

    //
    // Trigger the computation by counting the ranks. An alternative is to
    // call collect(), which would also gather all the data into the driver
    // as part of the measured operation. A typical application would probably
    // iterate over a (potentially large) result (which is what count() will
    // do) instead of collecting it into one place.
    //
    val rankCount: Int = ranks.count().toInt

    new BenchmarkResult {
      //
      // Validate the result. Check the number of ranks first, and then the
      // hash of the string representation of the ranks. Round the ranks to
      // 8 decimal places and order them by the web site id to avoid numerical
      // instability issues on different platforms.
      //
      override def validate() = {
        Assert.assertEquals(expectedRankCountParam, rankCount, "ranks count")

        val rankLines = ranks
          .sortByKey()
          .map {
            case (url, rank) => f"$url $rank%.8f"
          }
          .collect
          .toList

        Validators.hashing(expectedRankHashParam, rankLines.asJava).validate()
      }
    }
  }

  override def tearDownAfterAll(c: BenchmarkContext): Unit = {
    tearDownSparkContext(sc)
    c.deleteTempDir(tempDirPath)
  }
}
