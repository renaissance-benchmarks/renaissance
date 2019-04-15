package org.renaissance.apache.spark

import java.nio.charset.StandardCharsets
import java.nio.file.{Path, Paths}
import java.util.zip.ZipInputStream

import org.apache.commons.io.{FileUtils, IOUtils}
import org.apache.spark.{SparkConf, SparkContext}
import org.apache.spark.rdd.RDD
import org.renaissance.{Config, License, RenaissanceBenchmark}

class PageRank extends RenaissanceBenchmark {
  def description = "Runs a number of PageRank iterations, using RDDs."

  override def defaultRepetitions = 20

  override def licenses = License.create(License.APACHE2)

  val ITERATIONS = 2

  val THREAD_COUNT = Runtime.getRuntime.availableProcessors

  val pageRankPath = Paths.get("target", "page-rank")

  val outputPath = pageRankPath.resolve("output")

  val inputFile = "web-berkstan.txt.zip"

  val bigInputFile = pageRankPath.resolve("bigfile.txt")

  var sc: SparkContext = null

  var links: RDD[(String, Iterable[String])] = null

  var ranks: RDD[(String, Double)] = null

  var tempDirPath: Path = null

  override def setUpBeforeAll(c: Config): Unit = {
    tempDirPath = RenaissanceBenchmark.generateTempDir("page_rank")
    val conf = new SparkConf()
      .setAppName("page-rank")
      .setMaster(s"local[$THREAD_COUNT]")
      .set("spark.local.dir", tempDirPath.toString)
    sc = new SparkContext(conf)
    sc.setLogLevel("ERROR")

    // Prepare input.
    FileUtils.deleteDirectory(pageRankPath.toFile)
    val zis = new ZipInputStream(this.getClass.getResourceAsStream("/" + inputFile))
    zis.getNextEntry()
    val text = IOUtils.toString(zis, StandardCharsets.UTF_8)
    FileUtils.write(bigInputFile.toFile, text, StandardCharsets.UTF_8, true)

    // Load data.
    val lines = sc.textFile(bigInputFile.toString)
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
    sc.stop()
    RenaissanceBenchmark.deleteTempDir(tempDirPath)
  }
}
