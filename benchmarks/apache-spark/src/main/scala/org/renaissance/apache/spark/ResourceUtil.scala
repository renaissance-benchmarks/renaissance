package org.renaissance.apache.spark

import java.io.FileNotFoundException
import java.io.InputStream
import java.net.URL
import java.nio.charset.StandardCharsets
import java.nio.file.Files
import java.nio.file.Path
import java.nio.file.StandardCopyOption
import java.util.zip.ZipInputStream
import scala.io.BufferedSource
import scala.io.Source

private object ResourceUtil {

  /**
   * Writes a resource associated with the {@link ResourceUtil} class
   * to a file, replacing an existing file.
   *
   * @param resourceName path to the resource
   * @param file path the output file
   * @return {@link Path} path to the output file
   */
  def writeResourceToFile(resourceName: String, file: Path) = {
    val resourceStream = getResourceStream(resourceName)
    Files.copy(resourceStream, file, StandardCopyOption.REPLACE_EXISTING)

    file
  }

  /**
   * Loads a file from the given [[url]] as a sequence of lines.
   *
   * @param url input file [[URL]]
   * @return a sequence of lines
   */
  def linesFromUrl(url: URL): Seq[String] = {
    val source = Source.fromURL(url)
    try {
      source.getLines().to[Seq]
    } finally {
      source.close()
    }
  }

  /**
   * Creates a {@link Source} from a file within a ZIP resource
   * associated with the {@link ResourceUtil} class.
   *
   * @param resourceName path to the ZIP resource
   * @param entryName name of the ZIP entry
   * @return {@link Source} instance for the given file within a ZIP
   */
  def sourceFromZipResource(resourceName: String, entryName: String): BufferedSource = {
    val zis = new ZipInputStream(getResourceStream(resourceName))
    try {
      Iterator
        .continually(zis.getNextEntry)
        .takeWhile(_ != null)
        .filterNot(_.isDirectory)
        .find(_.getName.equalsIgnoreCase(entryName))
        .map(_ => Source.fromInputStream(zis, StandardCharsets.UTF_8.name))
        .getOrElse {
          throw new FileNotFoundException(
            s"file '$entryName' not found in resource '$resourceName'"
          )
        }
    } catch {
      // Close the stream and propagate the exception
      case e: Throwable =>
        zis.close()
        throw e
    }
  }

  private def getResourceStream(resourceName: String): InputStream = {
    val is = getClass.getResourceAsStream(resourceName)
    if (is != null) {
      return is
    }

    throw new FileNotFoundException(s"resource '$resourceName' not found")
  }
}
