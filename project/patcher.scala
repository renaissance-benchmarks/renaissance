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
import java.security.MessageDigest
import java.security.NoSuchAlgorithmException
import java.util.jar.JarEntry
import java.util.jar.JarFile
import java.util.jar.JarInputStream
import java.util.jar.JarOutputStream
import java.util.jar.Manifest

import org.objectweb.asm.ClassReader
import org.objectweb.asm.ClassVisitor
import org.objectweb.asm.ClassWriter
import org.objectweb.asm.MethodVisitor
import org.objectweb.asm.Opcodes

object Patcher {

  type Method = (File, File, Logger) => Try[Unit]

  /**
   * Creates a task that produces a patched version of a specific JAR file using the
   * given `patcher`. The task searches a project's runtime dependencies for the JAR
   * file and creates a patched version in the project's 'target/patched' directory
   * (unless the patched version already exists).
   */
  def generatePatchedJarTask(
    jarPrefix: String,
    patcher: Patcher.Method
  ): Def.Initialize[Task[Seq[File]]] =
    Def.task {
      val log = sLog.value
      val projectName = (ThisProject / name).value
      val targetDir = (Compile / target).value / "patched"
      val dependencyJars = (Runtime / dependencyClasspathAsJars).value

      dependencyJars.map(_.data).filter(f => f.name.startsWith(jarPrefix)).map { originalJar =>
        val patchedJar = targetDir / originalJar.name
        if (!patchedJar.exists()) {
          log.info(s"Patching ${originalJar.name} in $projectName")
          IO.createDirectory(targetDir)

          val temporaryJar = patchedJar.getParentFile / (patchedJar.name + ".tmp")
          patcher(originalJar, temporaryJar, log) match {
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

  /**
   * Creates a task that modifies a project's runtime dependencies to use patched JAR files
   * if they exist in the 'target/patched' subdirectory. The matching is performed using
   * the JAR file names (without path prefix).
   *
   * The patched JAR files must exist before this task is executed. This can be achieved by
   * adding a dependency on one or more instances of the [[generatePatchedJarTask()]] above.
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

  /**
   * Generates a patched Hadoop Client API jar, which modifies the 'UserGroupInformation' class
   * to avoid calling deprecated Java Security API. This allows using Spark with Java 23+
   * without having to specify '-Djava.security.manager=allow' on the command line, which
   * in turn allows running with GraalVM Native Image.
   */
  def patchHadoopClientApiJar(
    inputJarFile: File,
    outputJarFile: File,
    log: Logger
  ): Try[Unit] = {
    Using.Manager { use =>
      val jis = use(new JarInputStream(new FileInputStream(inputJarFile)))
      val jos = use(new JarOutputStream(new FileOutputStream(outputJarFile)))

      // Enable the multi-release attribute in the output jar.
      val manifest = createOrUpdateManifest(Option(jis.getManifest));
      jos.putNextEntry(new JarEntry(JarFile.MANIFEST_NAME));
      manifest.write(jos);
      jos.closeEntry()

      // Copy JAR entries, adding a patched UserGroupInformation class.
      lazyJarEntries(jis).foreach { entry =>
        val inputBytes = jis.readAllBytes
        jis.closeEntry()

        storeJarEntry(inputBytes, entry, jos)

        // Include patched UserGroupInformation class for Java 23+, which will
        // pick it up from the version-specific location in multi-release jar.
        if ("org/apache/hadoop/security/UserGroupInformation.class".equals(entry.getName)) {
          log.debug(s"processing byte code in $entry")
          ensureMatchingDigest(inputBytes, "md5:a6be5d7798cda1e3e854feb0edbdaacf", "input")

          val outputBytes = patchUserGroupInformationClass(inputBytes)
          ensureMatchingDigest(outputBytes, "md5:16a321b5a4ffa65946da39bccfc6883f", "output")

          val outputEntry = new JarEntry(s"META-INF/versions/23/${entry.getName}")
          log.debug(s"storing byte code in $outputEntry")
          storeJarEntry(outputBytes, outputEntry, jos)
        }
      }
    }
  }

  private def patchUserGroupInformationClass(bytes: Array[Byte]) = {
    val classReader = new ClassReader(bytes)
    val classWriter = new ClassWriter(
      classReader,
      ClassWriter.COMPUTE_FRAMES | ClassWriter.COMPUTE_MAXS
    )
    val classPatcher = new UserGroupInformationPatcher(Opcodes.ASM9, classWriter)
    classReader.accept(classPatcher, ClassReader.EXPAND_FRAMES)
    classWriter.toByteArray
  }

  private class UserGroupInformationPatcher(api: Int, cv: ClassVisitor)
    extends ClassVisitor(api: Int, cv: ClassVisitor) {

    override def visitMethod(
      access: Int,
      name: String,
      descriptor: String,
      signature: String,
      exceptions: Array[String]
    ) = {
      val mv = super.visitMethod(access, name, descriptor, signature, exceptions)

      // Modify only the getCurrentUser method.
      if (isGetCurrentUserMethod(name, descriptor)) {
        new GetCurrentUserMethodPatcher(Opcodes.ASM9, mv);
      } else {
        mv
      }
    }

    private def isGetCurrentUserMethod(name: String, descriptor: String) = {
      "getCurrentUser".equals(name) &&
      "()Lorg/apache/hadoop/security/UserGroupInformation;".equals(descriptor)
    }
  }

  private class GetCurrentUserMethodPatcher(api: Int, mv: MethodVisitor)
    extends MethodVisitor(api: Int, mv: MethodVisitor) {

    override def visitMethodInsn(
      opcode: Int,
      owner: String,
      name: String,
      descriptor: String,
      isInterface: Boolean
    ): Unit = {
      // Check if the method being called is Subject.getSubject
      if (isGetSubjectMethod(owner, name, descriptor)) {
        if (opcode != Opcodes.INVOKESTATIC) {
          throw new AssertionError(s"$owner.$name invocation is not static")
        }

        // Remove the argument from the stack.
        super.visitInsn(Opcodes.POP)
        super.visitMethodInsn(
          opcode,
          owner,
          "current",
          "()Ljavax/security/auth/Subject;",
          false
        )
      } else {
        super.visitMethodInsn(opcode, owner, name, descriptor, isInterface)
      }
    }

    private def isGetSubjectMethod(owner: String, name: String, descriptor: String) = {
      "javax/security/auth/Subject".equals(owner) &&
      "getSubject".equals(name) &&
      "(Ljava/security/AccessControlContext;)Ljavax/security/auth/Subject;".equals(descriptor)
    }
  }

  //

  /**
   * Generates a patched Spark Unsafe jar, which modifies the 'Platform' class
   * to avoid looking up internal cleaner class removed in Java 26-ea+6.
   * This allows using Spark with Java 26+ (until it eventually catches up).
   */
  def patchSparkUnsafeJar(inputJarFile: File, outputJarFile: File, log: Logger): Try[Unit] = {
    Using.Manager { use =>
      val jis = use(new JarInputStream(new FileInputStream(inputJarFile)))
      val jos = use(new JarOutputStream(new FileOutputStream(outputJarFile)))

      // Enable the multi-release attribute in the output jar.
      val manifest = createOrUpdateManifest(Option(jis.getManifest));
      jos.putNextEntry(new JarEntry(JarFile.MANIFEST_NAME));
      manifest.write(jos);
      jos.closeEntry()

      // Copy JAR entries, adding a patched UserGroupInformation class.
      lazyJarEntries(jis).foreach { entry =>
        val inputBytes = jis.readAllBytes
        jis.closeEntry()

        storeJarEntry(inputBytes, entry, jos)

        // Include patched UserGroupInformation class for Java 23+, which will
        // pick it up from the version-specific location in multi-release jar.
        if ("org/apache/spark/unsafe/Platform.class".equals(entry.getName)) {
          log.debug(s"processing byte code in $entry")
          ensureMatchingDigest(inputBytes, "md5:4e794b76d4071d15f2de492b93d15a01", "input")

          val outputBytes = patchPlatformClassInitializer(inputBytes)
          ensureMatchingDigest(outputBytes, "md5:04d3fc3d59042f2a8a92dd033f3ad0f8", "output")

          val outputEntry = new JarEntry(s"META-INF/versions/26/${entry.getName}")
          log.debug(s"storing byte code in $outputEntry")
          storeJarEntry(outputBytes, outputEntry, jos)
        }
      }
    }
  }

  private def patchPlatformClassInitializer(bytes: Array[Byte]) = {
    val classReader = new ClassReader(bytes)
    val classWriter = new ClassWriter(
      classReader,
      ClassWriter.COMPUTE_FRAMES | ClassWriter.COMPUTE_MAXS
    )
    val classPatcher = new PlatformClassInitializerPatcher(Opcodes.ASM9, classWriter)
    classReader.accept(classPatcher, ClassReader.EXPAND_FRAMES)
    classWriter.toByteArray
  }

  private class PlatformClassInitializerPatcher(api: Int, cv: ClassVisitor)
    extends ClassVisitor(api: Int, cv: ClassVisitor) {

    override def visitMethod(
      access: Int,
      name: String,
      descriptor: String,
      signature: String,
      exceptions: Array[String]
    ) = {
      val mv = super.visitMethod(access, name, descriptor, signature, exceptions)

      // Modify only the static initializer method.
      if (isClassInitializer(name, descriptor)) {
        new CleanerFieldStorePatcher(Opcodes.ASM9, mv);
      } else {
        mv
      }
    }

    private def isClassInitializer(name: String, descriptor: String) = {
      "<clinit>".equals(name) && "()V".equals(descriptor)
    }
  }

  private class CleanerFieldStorePatcher(api: Int, mv: MethodVisitor)
    extends MethodVisitor(api: Int, mv: MethodVisitor) {

    override def visitFieldInsn(
      opcode: Int,
      owner: String,
      name: String,
      descriptor: String
    ): Unit = {
      // Check if the field being assigned is the static DBB_CLEANER_FIELD
      if (opcode == Opcodes.PUTSTATIC && isDbbCleanerField(owner, name, descriptor)) {
        //
        // Replace the argument on the stack with 'null'. Assigning 'null' to
        // the 'DBB_CLEANER_FIELD' cause the (failing) code trying to load the
        // 'jdk.internal.ref.Cleaner' class to be skipped.
        //
        // With the cleaner field unset, subsequent 'DirectByteBuffer' allocations
        // through the 'Platform.allocateDirectBuffer()' will use normal Java API.
        //
        super.visitInsn(Opcodes.POP)
        super.visitInsn(Opcodes.ACONST_NULL)
      }

      super.visitFieldInsn(opcode, owner, name, descriptor)
    }

    private def isDbbCleanerField(owner: String, name: String, descriptor: String) = {
      "org/apache/spark/unsafe/Platform".equals(owner) &&
      "DBB_CLEANER_FIELD".equals(name) &&
      "Ljava/lang/reflect/Field;".equals(descriptor)
    }
  }

  //

  private def createOrUpdateManifest(manifest: Option[Manifest]) = {
    val result = manifest.getOrElse(new Manifest)
    result.getMainAttributes.putValue("Multi-Release", "true")
    result
  }

  private def lazyJarEntries(initialJis: JarInputStream): LazyList[JarEntry] = {
    //
    // Provide the entries lazily!
    //
    // The consumer will want to access the bytes of the current entry, so the state
    // of the input stream must not change until the next entry is requested.
    //
    LazyList.unfold(initialJis) { jis =>
      Option(jis.getNextJarEntry).flatMap(entry => Some(entry, jis))
    }
  }

  private def ensureMatchingDigest(bytes: Array[Byte], expected: String, kind: String): Unit = {
    val actual = md5(bytes)
    if (!expected.equals(actual)) {
      throw new IllegalStateException(
        s"mismatching $kind class digest: expected=$expected, actual=$actual"
      )
    }
  }

  private def md5(bytes: Array[Byte]) =
    try {
      val digest = MessageDigest.getInstance("md5")
      val hexString = digest.digest(bytes).map("%02x".format(_)).mkString
      val algorithm = digest.getAlgorithm.toLowerCase
      s"$algorithm:$hexString"
    } catch {
      case e: NoSuchAlgorithmException => ""
    }

  private def storeJarEntry(bytes: Array[Byte], entry: JarEntry, jos: JarOutputStream): Unit = {
    jos.putNextEntry(entry)
    jos.write(bytes)
    jos.closeEntry()
  }

}
