package org.renaissance.scala.dotty

import java.io.{FileOutputStream, _}
import java.net.URLClassLoader
import java.util.zip.ZipInputStream

import org.apache.commons.io.IOUtils
import org.renaissance.{Config, License, RenaissanceBenchmark}

import scala.collection._

class Dotty extends RenaissanceBenchmark {
  def description = "Runs the Dotty compiler on a set of source code files."

  override def defaultRepetitions = 50

  def licenses = License.create(License.BSD3)

  private val zipPath = "/sources.zip"

  private val dottyPath = "target/dotty"

  private val sourceCodePath = dottyPath + "/src"

  private val outputPath = dottyPath + "/output"

  private var sources: mutable.Buffer[String] = null

  override def setUpBeforeAll(c: Config): Unit = {
    new File(outputPath).mkdirs()
    // Unzip sources.
    sources = mutable.Buffer[String]()
    val zis = new ZipInputStream(this.getClass.getResourceAsStream(zipPath))
    val target = new File(sourceCodePath)
    var nextEntry = zis.getNextEntry
    while (nextEntry != null) {
      val name = nextEntry.getName
      if (!name.endsWith("/")) {
        val f = new File(target, name)
        // create directories
        val parent = f.getParentFile
        if (parent != null) parent.mkdirs
        val targetStream = new FileOutputStream(f)
        IOUtils.copy(zis, targetStream)
        targetStream.close()
        sources += name
        nextEntry = zis.getNextEntry
      }
    }
  }

  override def runIteration(c: Config): Unit = {
    val paths: mutable.Seq[String] = sources
      .map(f => sourceCodePath + "/" + f)
    val args = Seq[String](
      "-bootclasspath",
      Thread.currentThread.getContextClassLoader
        .asInstanceOf[URLClassLoader]
        .getURLs
        .mkString(":"),
      "-language:implicitConversions",
      "-d",
      outputPath
    )
    paths.map(p => args :+ p).foreach(x => dotty.tools.dotc.Main.process(x.toArray))
  }
}
