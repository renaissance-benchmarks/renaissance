package org.renaissance.apache.spark

import java.io.FileOutputStream
import java.nio.file.Files
import java.nio.file.Path
import java.nio.file.Paths

import org.apache.commons.io.IOUtils
import org.apache.spark.SparkConf
import org.apache.spark.SparkContext
import org.apache.spark.rdd.RDD

trait SparkUtil {

  val portAllocationMaxRetries: Int = 16

  val winUtils = "/winutils.exe"

  def setUpSparkContext(
    dirPath: Path,
    threadsPerExecutor: Int,
    benchName: String
  ): SparkContext = {
    setUpHadoop(dirPath)

    //
    // We bind Spark explicitly to localhost to avoid all sorts of trouble:
    // https://github.com/renaissance-benchmarks/renaissance/issues/66
    //
    // However, setting spark.driver.bindAddress to "127.0.0.1" does not
    // seem to work on Spark 2.4.7, whereas setting spark.driver.host to
    // "localhost" or "127.0.0.1" does, so does setting the SPARK_LOCAL_IP
    // environment variable (but we cannot do it from here).
    //
    val conf = new SparkConf()
      .setAppName(benchName)
      .setMaster(s"local[$threadsPerExecutor]")
      .set("spark.driver.host", "localhost")
      .set("spark.driver.bindAddress", "127.0.0.1")
      .set("spark.local.dir", dirPath.toString)
      .set("spark.port.maxRetries", portAllocationMaxRetries.toString)
      .set("spark.executor.instances", "4")
      .set("spark.sql.warehouse.dir", dirPath.resolve("warehouse").toString)

    val sc = new SparkContext(conf)
    sc.setLogLevel("ERROR")
    sc
  }

  def tearDownSparkContext(sc: SparkContext): Unit = {
    if (sc != null) {
      sc.stop()
    }
  }

  /**
   * Spark version 2.4.7 uses Hadoop version 2.6.5. The dependencies
   * do not include a binary zip for Hadoop on Windows. Instead,
   * Renaissance includes winutils.exe as a resource, downloaded from
   * https://github.com/cdarlint/winutils/tree/master/hadoop-2.6.5/bin
   *
   * When updating Spark in Renaissance, the file must be upgraded to the
   * corresponding Hadoop version from https://github.com/cdarlint/winutils
   */
  def setUpHadoop(tempDirPath: Path): Any = {
    if (sys.props.get("os.name").toString.contains("Windows")) {
      val winutilsPath = Paths.get(tempDirPath.toAbsolutePath + "/bin")
      Files.createDirectories(winutilsPath)
      IOUtils.copy(
        this.getClass.getResourceAsStream(winUtils),
        new FileOutputStream(winutilsPath.toString + winUtils)
      )
      System.setProperty("hadoop.home.dir", tempDirPath.toAbsolutePath.toString)
    }
  }

  def ensureCaching[T](rdd: RDD[T]): Unit = {
    if (!rdd.getStorageLevel.useMemory) {
      throw new Exception("Spark RDD must be cached !")
    }
  }
}
