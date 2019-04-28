package org.renaissance.apache.spark

import java.nio.file.{ Path, Paths, Files }
import org.apache.commons.io.IOUtils
import java.io.FileOutputStream

object HadoopUtil {

  /* For Spark version on renaissance (2.0.0) the Hadoop version is 2.2.0
     For Windows, the binary zip is not included in the dependencies
     We include in the resource winutils.exe from
     https://github.com/srccodes/hadoop-common-2.2.0-bin
     If Spark version is updated in future releases of renaissance,
     the file must be upgraded to the corresponding Hadoop version
   */
  val inputFile = "/winutils.exe"

  def setUpHadoop(tempDirPath: Path):Any = {
    if (sys.props.get("os.name").toString.contains("Windows")) {
      val winutilsPath = Paths.get(tempDirPath.toAbsolutePath + "/bin")
      Files.createDirectories(winutilsPath)
      IOUtils.copy(
        this.getClass.getResourceAsStream(inputFile),
        new FileOutputStream(winutilsPath.toString + inputFile)
      )
      System.setProperty("hadoop.home.dir", tempDirPath.toAbsolutePath.toString)
    }
  }
}
