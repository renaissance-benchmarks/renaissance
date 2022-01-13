import sbt.File
import sbt.Logger
import sbt.io.IO
import sbt.io.Using

import java.io.FileOutputStream
import java.nio.file.Files
import java.nio.file.Path
import java.util.Properties

object Utils {

  def storeProperties(
    props: Properties,
    comments: String,
    file: sbt.File,
    maybeLog: Option[Logger]
  ) = {
    maybeLog.foreach { log => log.info(s"Writing $file ...") }

    // Create leading directories.
    Option(file.getParentFile).foreach { dir => IO.createDirectory(dir) }

    Using.fileOutputStream(append = false)(file) { fos =>
      props.store(fos, comments)
    }

    file
  }

  /**
   * Creates a symlink to the given script file. If the link file already
   * exists and is actually a symlink or, we just ensure that it points to
   * the given script file (i.e., we might overwrite the symlink target).
   * If the link file is a regular file, we refuse to overwrite it.
   */
  def installSymlink(scriptFile: File, linkFile: File, log: Logger): Unit = {
    val linkPath = linkFile.toPath
    val scriptPath = scriptFile.toPath

    if (Files.isSymbolicLink(linkPath)) {
      if (Files.isExecutable(linkPath) && Files.isSameFile(linkPath.toRealPath(), scriptPath)) {
        // The link already points to the given target.
        log.debug(s"symlink $linkFile already points to $scriptFile")
        return
      }

      // Delete the symlink so that it can be updated.
      Files.delete(linkPath)
    }

    if (Files.notExists(linkPath)) {
      // Force the symlink to point to the given target.
      val scriptRelPath = linkPath.getParent.relativize(scriptPath)
      log.info(s"installing $linkFile symlink to $scriptRelPath")
      Files.createSymbolicLink(linkPath, scriptRelPath)
    } else {
      log.warn(s"$linkFile is a regular file, symlink to $scriptFile NOT installed!")
    }
  }

  def asUnixPath(path: Path) = {
    import scala.jdk.CollectionConverters._
    path.asScala.mkString("/")
  }

}
