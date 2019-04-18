package org.renaissance.apache.spark

import java.io.File
import java.nio.charset.StandardCharsets
import java.util.zip.ZipInputStream

import org.apache.commons.io.IOUtils

object ZipResourceUtil {

  def readZipFromResourceToText(resourceName: String): String = {
    val zis = new ZipInputStream(this.getClass.getResourceAsStream(File.separator  + resourceName))
    zis.getNextEntry()
    IOUtils.toString(zis, StandardCharsets.UTF_8)
  }

}
