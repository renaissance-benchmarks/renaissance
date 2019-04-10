package org.renaissance.apache.spark

import java.io.File
import java.nio.charset.StandardCharsets
import java.util.zip.ZipInputStream
import org.apache.commons.io.FileUtils
import org.apache.commons.io.IOUtils
import org.apache.spark.SparkConf
import org.apache.spark.SparkContext
import org.apache.spark.rdd.RDD
import org.renaissance.Config
import org.renaissance.License
import org.renaissance.RenaissanceBenchmark

class PageRank extends RenaissanceBenchmark {
  def description = "Runs a number of PageRank iterations, using RDDs."

  override def defaultRepetitions = 20

  override def licenses = License.create(License.APACHE2)

  val ITERATIONS = 2

  val THREAD_COUNT = Runtime.getRuntime.availableProcessors

  val pageRankPath = "target/page-rank"

  val outputPath = pageRankPath + "/output"

  val inputFile = "/web-berkstan.txt.zip"

  val bigInputFile = pageRankPath + "/bigfile.txt"

  var sc: SparkContext = null

  var links: RDD[(String, Iterable[String])] = null

  var ranks: RDD[(String, Double)] = null

  val tempDir: String = RenaissanceBenchmark.generateTempDir("page_rank")

  override def setUpBeforeAll(c: Config): Unit = {
    val conf = new SparkConf()
      .setAppName("page-rank")
      .setMaster(s"local[$THREAD_COUNT]")
      .set("spark.local.dir", tempDir)
    sc = new SparkContext(conf)
    sc.setLogLevel("ERROR")

    // Prepare input.
    FileUtils.deleteDirectory(new File(pageRankPath))
    val zis = new ZipInputStream(this.getClass.getResourceAsStream(inputFile))
    zis.getNextEntry()
    val text = IOUtils.toString(zis, StandardCharsets.UTF_8)
    FileUtils.write(new File(bigInputFile), text, StandardCharsets.UTF_8, true)

    // Load data.
    val lines = sc.textFile(bigInputFile)
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
    FileUtils.write(new File(outputPath), output, StandardCharsets.UTF_8, true)
    sc.stop()
    RenaissanceBenchmark.deleteTempDir(tempDir)
  }
}
