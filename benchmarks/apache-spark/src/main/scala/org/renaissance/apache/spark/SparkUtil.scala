package org.renaissance.apache.spark

import org.apache.spark.rdd.RDD
import org.apache.spark.SparkConf
import org.apache.spark.SparkContext
import org.renaissance.Benchmark.Name
import org.renaissance.BenchmarkContext

import java.nio.file.Files
import java.nio.file.Path

/**
 * A common trait for all Spark benchmarks. Provides shared Spark
 * setup code and other convenience methods.
 *
 * The common setup code requires that all Spark benchmarks define
 * `spark_executor_count` and `spark_threads_per_executor`
 * parameters, which determine the level of parallelism.
 */
trait SparkUtil {

  private val portAllocationMaxRetries: Int = 16

  private val winutilsName = "winutils.exe"
  private val winutilsSize = 109568

  protected var sparkContext: SparkContext = _

  def setUpSparkContext(bc: BenchmarkContext): SparkContext = {
    val scratchDir = bc.scratchDirectory()
    setUpHadoop(scratchDir.resolve("hadoop"))

    //
    // We bind Spark explicitly to localhost to avoid all sorts of trouble:
    // https://github.com/renaissance-benchmarks/renaissance/issues/66
    //
    // However, setting spark.driver.bindAddress to "127.0.0.1" does not
    // seem to work on Spark 2.4.7, whereas setting spark.driver.host to
    // "localhost" or "127.0.0.1" does, so does setting the SPARK_LOCAL_IP
    // environment variable (but we cannot do it from here).
    //

    val benchmarkName = getClass.getDeclaredAnnotation(classOf[Name]).value
    val executorCount = bc.parameter("spark_executor_count").toPositiveInteger
    val threadCount = bc.parameter("spark_executor_thread_count").toPositiveInteger

    val conf = new SparkConf()
      .setAppName(benchmarkName)
      .setMaster(s"local[$threadCount]")
      .set("spark.driver.host", "localhost")
      .set("spark.driver.bindAddress", "127.0.0.1")
      .set("spark.local.dir", scratchDir.toString)
      .set("spark.port.maxRetries", portAllocationMaxRetries.toString)
      .set("spark.executor.instances", s"$executorCount")
      .set("spark.sql.warehouse.dir", scratchDir.resolve("warehouse").toString)

    sparkContext = new SparkContext(conf)
    sparkContext.setLogLevel("ERROR")
    sparkContext
  }

  def tearDownSparkContext(sc: SparkContext): Unit = {
    if (sc != null) {
      sc.stop()
    }
  }

  def tearDownSparkContext(): Unit = {
    tearDownSparkContext(sparkContext)
    sparkContext = null
  }

  /**
   * Spark version 3.1.1 uses Hadoop version 3.2.0. The dependencies
   * do not include a binary zip for Hadoop on Windows. Instead,
   * Renaissance includes winutils.exe as a resource, downloaded from
   * https://github.com/cdarlint/winutils/tree/master/hadoop-3.2.0/bin
   *
   * When updating Spark in Renaissance, the file must be upgraded to the
   * corresponding Hadoop version from https://github.com/cdarlint/winutils
   */
  private def setUpHadoop(hadoopHomeDir: Path): Unit = {
    if (sys.props.get("os.name").toString.contains("Windows")) {
      val hadoopHomeDirAbs = hadoopHomeDir.toAbsolutePath
      val winutilsDir = Files.createDirectories(hadoopHomeDirAbs.resolve("bin"))
      val winutilsStream = getClass.getResourceAsStream("/" + winutilsName)

      try {
        val bytesWritten = Files.copy(
          winutilsStream,
          winutilsDir.resolve(winutilsName)
        )

        if (bytesWritten != winutilsSize) {
          throw new Exception(
            s"Wrong winutils.exe size: expected $winutilsSize, written $bytesWritten"
          )
        }
      } finally {
        // This may mask a try-block exception, but at least it will fail anyway.
        winutilsStream.close()
      }

      System.setProperty("hadoop.home.dir", hadoopHomeDirAbs.toString)
    }
  }

  def ensureCached[T](rdd: RDD[T]): RDD[T] = {
    if (!rdd.getStorageLevel.useMemory) {
      throw new Exception("Spark RDD must be cached!")
    }

    rdd
  }
}
