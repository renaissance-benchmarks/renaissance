package org.renaissance.apache.spark

import java.io.FileNotFoundException
import java.nio.charset.StandardCharsets
import java.util.zip.ZipInputStream

import scala.io.BufferedSource
import scala.io.Source

object ZipResourceUtil {

  def sourceFromZipResource(entryName: String, resourceName: String): BufferedSource = {
    val is = this.getClass.getResourceAsStream("/" + resourceName)
    if (is == null) {
      throw new FileNotFoundException(
        s"resource '$resourceName' not found"
      )
    }

    val zis = new ZipInputStream(is)
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

}
