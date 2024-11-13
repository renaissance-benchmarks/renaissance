package org.renaissance.apache.spark

import java.io.FileNotFoundException
import java.io.InputStream
import java.net.URL
import java.nio.charset.StandardCharsets
import java.nio.file.Files
import java.nio.file.Path
import java.nio.file.{StandardOpenOption => OpenOption}
import java.util.zip.ZipInputStream
import scala.io.BufferedSource
import scala.io.Source

private object ResourceUtil {

  /**
   * Writes the resource associated with the [[ResourceUtil]] class
   * to a file, replacing an existing file.
   * Checks that the file size is the same as expected.
   *
   * @param resourceName path to the resource
   * @param file path the output file
   * @param expectedSizeBytes Expected file size in bytes
   * @return [[Path]] to the output file
   */
  def writeResourceToFileCheckSize(resourceName: String, file: Path, expectedSizeBytes: Int) = {
    val stream = getClass.getResourceAsStream(resourceName)
    try {
      val bytesWritten = Files.copy(stream, file)

      if (bytesWritten != expectedSizeBytes) {
        throw new Exception(
          s"Wrong $file size: expected $expectedSizeBytes, written $bytesWritten bytes."
        )
      }
    } finally {
      // This may mask a try-block exception, but at least it will fail anyway.
      stream.close()
    }

    file
  }

  /**
   * Duplicates the lines from the input file a given number of times in the output file.
   *
   * @param url the [[URL]] of the input file
   * @param copyCount the number of times to duplicate the input
   * @param outputFile path to the output file
   * @return [[Path]] to the output file
   */
  def duplicateLinesFromUrl(url: URL, copyCount: Int, outputFile: Path): Path = {
    import scala.jdk.CollectionConverters._

    val lines = linesFromSource(Source.fromURL(url)).asJava

    for (_ <- 0 until copyCount) {
      Files.write(outputFile, lines, OpenOption.CREATE, OpenOption.APPEND)
    }

    outputFile
  }

  /**
   * Loads the contents of a [[Source]] as a sequence of lines and closes the source.
   *
   * @param source input [[Source]]
   * @return a sequence of lines
   */
  def linesFromSource(source: Source): Seq[String] = {
    try {
      source.getLines().toSeq
    } finally {
      source.close()
    }
  }

  /**
   * Creates a [[Source]] from a resource associated with the [[ResourceUtil]] class.
   *
   * @param resourceName path to the resource
   * @return a [[Source]] for the given resource
   */
  def sourceFromResource(resourceName: String): BufferedSource = {
    // Use an explicit codec to avoid influence of the environment.
    Source.fromURL(getClass.getResource(resourceName))(scala.io.Codec.UTF8)
  }

  /**
   * Creates a [[Source]] from a file within a ZIP resource
   * associated with the [[ResourceUtil]] class.
   *
   * @param resourceName path to the ZIP resource
   * @param entryName name of the ZIP entry
   * @return a [[Source]] for the given file within a ZIP
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
