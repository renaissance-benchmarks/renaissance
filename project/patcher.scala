import sbt._
import sbt.Keys._

import scala.util.Failure
import scala.util.Success
import scala.util.Try
import scala.util.Using
import scala.collection.compat.immutable.LazyList

import java.io.File
import java.io.FileInputStream
import java.io.FileOutputStream
import java.util.jar.JarEntry
import java.util.jar.JarFile
import java.util.jar.JarInputStream
import java.util.jar.JarOutputStream
import java.util.jar.Manifest

object Patcher {

  object Keys {

    val patchedJarPrefix = settingKey[String](
      "The file name prefix of the dependency JAR to be patched. Must be set in patch projects."
    ).withRank(KeyRanks.Invisible)

    val patchedJavaRelease = settingKey[Option[Int]](
      "Indicates that the patched JAR should retain the original classes and that the patch " +
        "classes should be added to the version-specific directory in a multi-release JAR. " +
        "If unset, the original classes in the common location will be replaced."
    ).withRank(KeyRanks.Invisible)
  }

  //

  /**
   * Creates a task that produces a patched version of a specific JAR file
   * using classes produced by a separate "patch project".
   *
   * The task searches this project's runtime dependencies for the JAR file and
   * creates a patched version in the project's 'target/patched' directory
   * (unless the patched version already exists).
   */
  def patchJarUsingProjectClassesTask(patchProject: Project): Def.Initialize[Task[Seq[File]]] =
    Def.task {
      val projectName = (ThisProject / name).value
      val targetDir = (Compile / target).value / "patched"
      val dependencyJars = (Runtime / dependencyClasspathAsJars).value

      // Make sure the patch project gets compiled.
      val patchCompilation = (patchProject / Compile / compile).value

      // Load settings from the patch project.
      val jarPrefix = (patchProject / Keys.patchedJarPrefix).value
      val targetRelease = (patchProject / Keys.patchedJavaRelease).value
      val patchClassesDir = (patchProject / Compile / classDirectory).value
      val patchClasses = collectPatchClasses(patchClassesDir)

      // Create a patcher that replaces JAR entries with patch project classes.
      new JarFilePatcher(sLog.value) {
        override def enableMultiRelease: Boolean = targetRelease.isDefined

        override def patchJarEntry(
          entry: JarEntry,
          bytes: Array[Byte]
        ): Seq[(JarEntry, Array[Byte])] = {
          patchClasses.get(entry.getName) match {
            case Some(patchFile) =>
              val patchBytes = IO.readBytes(patchFile)

              targetRelease match {
                case Some(version) =>
                  val patchEntry = new JarEntry(s"META-INF/versions/$version/${entry.getName}")
                  // Original entry and version-specific patch entry.
                  log.debug(s"copying $entry and adding $patchEntry")
                  Seq((entry, bytes), (patchEntry, patchBytes))
                case None =>
                  // Replaced original entry.
                  log.debug(s"replacing $entry")
                  Seq((entry, patchBytes))
              }
            case None =>
              // Original entry.
              log.verbose(() => s"copying $entry")
              Seq((entry, bytes))
          }
        }
      }.createdPatchedJar(jarPrefix, dependencyJars, targetDir, projectName)
    }

  private def collectPatchClasses(patchClassesDir: File) = {
    val classFiles = (patchClassesDir ** "*.class").filter(_.isFile).get
    classFiles.map(file => (file.relativeTo(patchClassesDir).map(_.toString).get, file)).toMap
  }

  //

  /**
   * Creates a task that modifies a project's runtime dependencies to use patched JAR files
   * if they exist in the 'target/patched' subdirectory. The matching is performed using
   * the JAR file names (without path prefix).
   *
   * The patched JAR files must exist before this task is executed. This is best achieved by
   * adding a dependency on [[patchJarUsingProjectClassesTask()]] instances above.
   *
   * Note that this does not change compile dependencies.
   */
  def remapPatchedJarFilesTask: Def.Initialize[Task[Classpath]] =
    Def.task {
      val log = sLog.value
      val targetDir = (Compile / target).value / "patched"
      val patchedJars = (targetDir * "*").get().map(file => (file.name, file)).toMap
      val projectName = (ThisProject / name).value
      val classPath = (Runtime / dependencyClasspathAsJars).value

      classPath.map { attributedFile =>
        attributedFile.map { sourceJarFile =>
          // Remap source JARs for which we find a match in the "patched" directory,
          // otherwise return the original JAR (the fold default).
          patchedJars.get(sourceJarFile.name).fold(sourceJarFile) { patchedJarFile =>
            log.info(s"Using patched ${sourceJarFile.name} in $projectName")
            patchedJarFile
          }
        }
      }
    }

  //

  /**
   * Simple JAR file patcher. Finds a JAR matching the given prefix among given dependency
   * JAR files and creates a patched variant of the JAR file. For each entry from the
   * original JAR file, the [[patchJarEntry()]] method determines what to put in the
   * patched JAR file.
   */
  private abstract class JarFilePatcher(val log: Logger) {

    final def createdPatchedJar(
      jarPrefix: String,
      dependencyJars: Classpath,
      targetDir: File,
      projectName: String
    ) = {
      dependencyJars.map(_.data).filter(f => f.name.startsWith(jarPrefix)).map { originalJar =>
        val patchedJar = targetDir / originalJar.name
        if (!patchedJar.exists()) {
          log.info(s"Patching ${originalJar.name} in $projectName")
          IO.createDirectory(targetDir)

          val temporaryJar = patchedJar.getParentFile / (patchedJar.name + ".tmp")
          patchJarFile(originalJar, temporaryJar) match {
            case Success(_) =>
              IO.move(temporaryJar, patchedJar)
            case Failure(exception) =>
              throw new RuntimeException(
                s"Failed to patch ${originalJar.name} in $projectName: ${exception.getMessage}"
              )
          }
        } else {
          log.info(s"Found patched ${originalJar.name} in $projectName")
        }

        patchedJar
      }
    }

    private def patchJarFile(
      inputJarFile: File,
      outputJarFile: File
    ): Try[Unit] = {
      Using.Manager { use =>
        val jis = use(new JarInputStream(new FileInputStream(inputJarFile)))
        val jos = use(new JarOutputStream(new FileOutputStream(outputJarFile)))

        // Enable the multi-release attribute in the output JAR if desired.
        val manifest = createOrUpdateManifest(Option(jis.getManifest), enableMultiRelease);
        jos.putNextEntry(new JarEntry(JarFile.MANIFEST_NAME));
        manifest.write(jos);
        jos.closeEntry()

        // Copy original/patched JAR entries returned by the patcher.
        lazyJarEntries(jis).foreach { entry =>
          val inputBytes = jis.readAllBytes
          jis.closeEntry()

          patchJarEntry(entry, inputBytes).foreach {
            case (outputEntry, outputBytes) =>
              storeJarEntry(outputEntry, outputBytes, jos)
          }
        }
      }
    }

    /**
     * Determines whether to create a multi-release enabled JAR.
     *
     * Subclasses need to implement this.
     */
    protected def enableMultiRelease: Boolean

    private def createOrUpdateManifest(manifest: Option[Manifest], multiRelease: Boolean) = {
      val result = manifest.getOrElse(new Manifest)
      result.getMainAttributes.putValue("Multi-Release", multiRelease.toString)
      result
    }

    private def lazyJarEntries(initialJis: JarInputStream): LazyList[JarEntry] = {
      //
      // Provide the entries lazily!
      //
      // The consumer will want to access the bytes of the current entry, so the state
      // of the input stream MUST NOT change until the next entry is requested.
      //
      LazyList.unfold(initialJis) { jis =>
        Option(jis.getNextJarEntry).flatMap(entry => Some(entry, jis))
      }
    }

    /**
     * Patches a single JAR entry. The method is expected to return zero or more
     * entries to be stored in the patched JAR.
     *
     * Subclasses need to implement this.
     */
    protected def patchJarEntry(
      entry: JarEntry,
      bytes: Array[Byte]
    ): Seq[(JarEntry, Array[Byte])]

    private def storeJarEntry(
      entry: JarEntry,
      bytes: Array[Byte],
      jos: JarOutputStream
    ): Unit = {
      jos.putNextEntry(entry)
      jos.write(bytes)
      jos.closeEntry()
    }

  }

}
