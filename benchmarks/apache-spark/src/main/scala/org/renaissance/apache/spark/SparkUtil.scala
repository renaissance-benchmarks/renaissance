package org.renaissance.apache.spark

import org.apache.log4j.Level
import org.apache.log4j.Logger
import org.apache.spark.SparkContext
import org.apache.spark.rdd.RDD
import org.apache.spark.sql.Dataset
import org.apache.spark.sql.SparkSession
import org.apache.spark.storage.StorageLevel
import org.renaissance.Benchmark.Name
import org.renaissance.BenchmarkContext

import java.nio.file.Files
import java.nio.file.Path
import scala.reflect.ClassTag

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

  // Copied from https://github.com/cdarlint/winutils
  // The mapping is filename to its size (for a basic sanity checking)
  private val hadoopExtrasForWindows = Map(
    "winutils.exe" -> 112640,
    "hadoop.dll" -> 85504
  )

  // Windows libraries that should be System.load()-ed
  private val hadoopPreloadedLibsForWindows = Seq(
    "hadoop.dll"
  )

  private val sparkLogLevel = Level.WARN
  private val jettyLogLevel = Level.WARN

  protected var sparkSession: SparkSession = _
  protected def sparkContext: SparkContext = sparkSession.sparkContext

  def setUpSparkContext(bc: BenchmarkContext, useCheckpointDir: Boolean = false): Unit = {
    setUpLoggers(sparkLogLevel, jettyLogLevel)

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
    val threadLimit = bc.parameter("spark_thread_limit").toPositiveInteger
    val cpuCount = Runtime.getRuntime.availableProcessors()
    val threadCount = Math.min(threadLimit, cpuCount)

    sparkSession = SparkSession
      .builder()
      .appName(benchmarkName)
      .master(s"local[$threadCount]")
      .config("spark.driver.host", "localhost")
      .config("spark.driver.bindAddress", "127.0.0.1")
      .config("spark.local.dir", scratchDir.toString)
      .config("spark.port.maxRetries", portAllocationMaxRetries.toString)
      .config("spark.sql.warehouse.dir", scratchDir.resolve("warehouse").toString)
      .getOrCreate()

    if (useCheckpointDir) {
      sparkContext.setCheckpointDir(scratchDir.resolve("checkpoints").toString)
    }

    sparkContext.setLogLevel(sparkLogLevel.toString)
    println(
      s"NOTE: '$benchmarkName' benchmark uses Spark local executor with $threadCount (out of $cpuCount) threads."
    )
  }

  def createRddFromCsv[T: ClassTag](
    lines: RDD[String],
    hasHeader: Boolean,
    delimiter: String,
    mapper: Array[String] => T
  ) = {
    val linesWithoutHeader = if (hasHeader) dropFirstLine(lines) else lines
    linesWithoutHeader.map(_.split(delimiter)).map(mapper).filter(_ != null)
  }

  private def dropFirstLine(lines: RDD[String]): RDD[String] = {
    val first = lines.first
    lines.filter { line => line != first }
  }

  def tearDownSparkContext(): Unit = {
    sparkSession.close()
  }

  /**
   * Spark version 3.1.2 uses Hadoop version 3.2.0. The dependencies
   * do not include a binary zip for Hadoop on Windows. Instead,
   * Renaissance includes winutils.exe as a resource, downloaded from
   * https://github.com/cdarlint/winutils/tree/master/hadoop-3.2.0/bin
   *
   * When updating Spark in Renaissance, the file must be updated to the
   * corresponding Hadoop version from https://github.com/cdarlint/winutils
   *
   * Also don't forget to update [[winutilsSize]] to match the binary.
   */
  private def setUpHadoop(hadoopHomeDir: Path): Unit = {
    if (sys.props.get("os.name").toString.contains("Windows")) {
      val hadoopHomeDirAbs = hadoopHomeDir.toAbsolutePath
      val hadoopBinDir = Files.createDirectories(hadoopHomeDirAbs.resolve("bin"))

      for ((filename, expectedSizeBytes) <- hadoopExtrasForWindows) {
        ResourceUtil.writeResourceToFileCheckSize(
          "/" + filename,
          hadoopBinDir.resolve(filename),
          expectedSizeBytes
        )
      }

      for (filename <- hadoopPreloadedLibsForWindows) {
        System.load(hadoopBinDir.resolve(filename).toString)
      }
      System.setProperty("hadoop.home.dir", hadoopHomeDirAbs.toString)
    }
  }

  def ensureCached[T](rdd: RDD[T]): RDD[T] = {
    assume(
      rdd.getStorageLevel == StorageLevel.NONE,
      "Storage level should be NONE before calling ensureCached()"
    )
    rdd.persist(StorageLevel.MEMORY_ONLY)
  }

  def ensureCached[T](ds: Dataset[T]): Dataset[T] = {
    assume(
      ds.storageLevel == StorageLevel.NONE,
      "Storage level should be NONE before calling ensureCached()"
    )
    ds.persist(StorageLevel.MEMORY_ONLY)
  }

  private def setUpLoggers(sparkLevel: Level, jettyLevel: Level) = {
    Logger.getLogger("org.apache.spark").setLevel(sparkLevel)
    Logger.getLogger("org.eclipse.jetty.server").setLevel(jettyLevel)
  }

}
