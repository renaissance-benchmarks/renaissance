package org.renaissance.apache.spark

import java.io.FileOutputStream
import java.nio.file.Files
import java.nio.file.Path
import java.nio.file.Paths

import org.apache.commons.io.IOUtils
import org.apache.spark.SparkConf
import org.apache.spark.SparkContext
import org.renaissance.RenaissanceBenchmark

trait SparkUtil {

  val portAllocationMaxRetries: Int = 16

  val winUtils = "/winutils.exe"

  def setUpSparkContext(dirPath: Path, thread_count: Int): SparkContext = {
    setUpHadoop(dirPath)
    val conf = new SparkConf()
      .setAppName(RenaissanceBenchmark.kebabCase(this.getClass.getSimpleName))
      .setMaster(s"local[$thread_count]")
      .set("spark.local.dir", dirPath.toString)
      .set("spark.port.maxRetries", portAllocationMaxRetries.toString)
      .set("spark.driver.bindAddress", "127.0.0.1")
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
   * For Spark version on renaissance (2.0.0) the Hadoop version is 2.2.0
   * For Windows, the binary zip is not included in the dependencies
   * We include in the resource winutils.exe from
   * https://github.com/srccodes/hadoop-common-2.2.0-bin
   * If Spark version is updated in future releases of renaissance,
   * the file must be upgraded to the corresponding Hadoop version.
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
}
