package org.renaissance.apache.spark

import java.nio.charset.StandardCharsets
import java.nio.file.Path
import java.nio.file.Paths

import org.apache.commons.io.FileUtils
import org.apache.spark.SparkContext
import org.apache.spark.rdd.RDD
import org.renaissance.Config
import org.renaissance.License
import org.renaissance.RenaissanceBenchmark
import org.renaissance.Benchmark._

import scala.collection.immutable.StringOps

@Name("page-rank")
@Group("apache-spark")
@Summary("Runs a number of PageRank iterations, using RDDs.")
@Licenses(Array(License.APACHE2))
@Repetitions(20)
class PageRank extends RenaissanceBenchmark with SparkUtil {

  // TODO: Consolidate benchmark parameters across the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/27

  var ITERATIONS = 2

  val THREAD_COUNT = Runtime.getRuntime.availableProcessors

  // TODO: Unify handling of scratch directories throughout the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/13

  val pageRankPath = Paths.get("target", "page-rank")

  val outputPath = pageRankPath.resolve("output")

  val inputFile = "web-berkstan.txt.zip"

  val bigInputFile = pageRankPath.resolve("bigfile.txt")

  var sc: SparkContext = null

  var links: RDD[(String, Iterable[String])] = null

  var ranks: RDD[(String, Double)] = null

  var tempDirPath: Path = null

  def prepareInput(c: Config) = {
    FileUtils.deleteDirectory(pageRankPath.toFile)
    var text = ZipResourceUtil.readZipFromResourceToText(inputFile)
    if (c.functionalTest) {
      val MAX_LINE = 5000
      val sublist =
        for ((line, num) <- new StringOps(text).lines.zipWithIndex if num < MAX_LINE) yield line
      text = sublist.toList.mkString("\n")
    }
    FileUtils.write(bigInputFile.toFile, text, StandardCharsets.UTF_8, true)
  }

  def loadData() = {
    var lines = sc.textFile(bigInputFile.toString)
    links = lines
      .map { line =>
        val parts = line.split("\\s+")
        (parts(0), parts(1))
      }
      .distinct()
      .groupByKey()
      .cache()
    ranks = links.mapValues(v => 1.0)
  }

  override def setUpBeforeAll(c: Config): Unit = {
    tempDirPath = RenaissanceBenchmark.generateTempDir("page_rank")
    sc = setUpSparkContext(tempDirPath, THREAD_COUNT)
    prepareInput(c)
    loadData()
  }

  override def runIteration(c: Config): Unit = {
    ranks = links.mapValues(v => 1.0)
    for (i <- 0 until ITERATIONS) {
      val contributions = links.join(ranks).values.flatMap {
        case (urls, rank) =>
          urls.map(url => (url, rank / urls.size))
      }
      ranks = contributions.reduceByKey(_ + _).mapValues(0.15 + 0.85 * _)
    }
    blackHole(ranks.count())
  }

  override def tearDownAfterAll(c: Config): Unit = {
    val output = ranks
      .collect()
      .map {
        case (url, rank) => s"$url $rank"
      }
      .mkString("\n")
    FileUtils.write(outputPath.toFile, output, StandardCharsets.UTF_8, true)
    tearDownSparkContext(sc)
    RenaissanceBenchmark.deleteTempDir(tempDirPath)
  }
}
