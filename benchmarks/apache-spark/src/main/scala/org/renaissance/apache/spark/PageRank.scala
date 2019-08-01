package org.renaissance.apache.spark

import java.nio.charset.StandardCharsets
import java.nio.file.Path
import java.nio.file.Paths

import org.apache.commons.io.FileUtils
import org.apache.spark.SparkContext
import org.apache.spark.rdd.RDD
import org.renaissance.Benchmark
import org.renaissance.Benchmark._
import org.renaissance.BenchmarkContext
import org.renaissance.BenchmarkResult
import org.renaissance.License

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
    new Parameter(name = "expected_rank_count", defaultValue = "598652")
  )
)
@Configurations(
  Array(
    new Configuration(
      name = "test",
      settings = Array("input_line_count = 5000", "expected_rank_count = 1661")
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

  private val ITERATIONS = 2

  // TODO: Unify handling of scratch directories throughout the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/13

  val pageRankPath = Paths.get("target", "page-rank")

  val outputPath = pageRankPath.resolve("output")

  val inputZipFile = "web-berkstan.txt.zip"

  val bigInputFile = pageRankPath.resolve("bigfile.txt")

  var sc: SparkContext = _

  var links: RDD[(String, Iterable[String])] = _

  var ranks: RDD[(String, Double)] = _

  var tempDirPath: Path = _

  def prepareInput(c: BenchmarkContext) = {
    FileUtils.deleteDirectory(pageRankPath.toFile)
    var inputText = ZipResourceUtil.readZipFromResourceToText(inputZipFile)
    if (inputLineCountParam >= 0) {
      inputText = inputText.linesWithSeparators.take(inputLineCountParam).mkString
    }

    FileUtils.write(bigInputFile.toFile, inputText, StandardCharsets.UTF_8, true)
  }

  def loadData() = {
    val lines = sc.textFile(bigInputFile.toString)
    links = lines
      .map { line =>
        val parts = line.split("\\s+")
        (parts(0), parts(1))
      }
      .distinct()
      .groupByKey()
      .cache()

//    ranks = links.mapValues(v => 1.0)
  }

  override def setUpBeforeAll(c: BenchmarkContext): Unit = {
    threadCountParam = c.intParameter("thread_count")
    expectedRankCountParam = c.intParameter("expected_rank_count")
    inputLineCountParam = c.intParameter("input_line_count")

    tempDirPath = c.generateTempDir("page_rank")
    sc = setUpSparkContext(tempDirPath, threadCountParam, "page-rank")
    prepareInput(c)
    loadData()
  }

  override def runIteration(c: BenchmarkContext): BenchmarkResult = {
    ranks = links.mapValues(v => 1.0)
    for (i <- 0 until ITERATIONS) {
      val contributions = links.join(ranks).values.flatMap {
        case (urls, rank) =>
          urls.map(url => (url, rank / urls.size))
      }
      ranks = contributions.reduceByKey(_ + _).mapValues(0.15 + 0.85 * _)
    }

    // TODO: add more sophisticated validation
    BenchmarkResult.simple("ranks count", expectedRankCountParam, ranks.count())
  }

  override def tearDownAfterAll(c: BenchmarkContext): Unit = {
    val output = ranks
      .collect()
      .map {
        case (url, rank) => s"$url $rank"
      }
      .mkString("\n")
    FileUtils.write(outputPath.toFile, output, StandardCharsets.UTF_8, true)

    tearDownSparkContext(sc)
    c.deleteTempDir(tempDirPath)
  }
}
