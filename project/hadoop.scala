import sbt.File
import sbt.Logger
import sbt.io.IO

import scala.util.Try
import scala.util.Failure
import scala.util.Success
import scala.util.Using
import scala.collection.compat.immutable.LazyList

import java.io.FileInputStream
import java.io.FileOutputStream
import java.security.MessageDigest
import java.security.NoSuchAlgorithmException
import java.util.jar.JarEntry
import java.util.jar.JarFile
import java.util.jar.JarInputStream
import java.util.jar.JarOutputStream
import java.util.jar.Manifest
import java.nio.file.Files
import java.nio.file.Path
import java.nio.file.Paths
import java.util.Properties

import org.objectweb.asm.ClassReader
import org.objectweb.asm.ClassVisitor
import org.objectweb.asm.ClassWriter
import org.objectweb.asm.MethodVisitor
import org.objectweb.asm.Opcodes

object Hadoop {

  def patchClientApiJar(inputJarFile: File, outputJarFile: File, log: Logger): Boolean = {
    Using.Manager { use =>
      val jis = use(new JarInputStream(new FileInputStream(inputJarFile)))
      val jos = use(new JarOutputStream(new FileOutputStream(outputJarFile)))

      // Enable the multi-release attribute in the output jar.
      val manifest = createOrUpdateManifest(Option(jis.getManifest()));
      jos.putNextEntry(new JarEntry(JarFile.MANIFEST_NAME));
      manifest.write(jos);
      jos.closeEntry()

      // Copy JAR entries, adding a patched UserGroupInformation class.
      lazyJarEntries(jis).foreach { entry =>
        val inputBytes = jis.readAllBytes
        jis.closeEntry

        storeJarEntry(jos, entry.getName, inputBytes)

        // Include patched UserGroupInformation class for Java 23+, which will
        // pick it up from the version-specific location in multi-release jar.
        if ("org/apache/hadoop/security/UserGroupInformation.class".equals(entry.getName)) {
          log.debug(s"processing byte code in $entry")
          ensureMatchingDigest(inputBytes, "md5:a6be5d7798cda1e3e854feb0edbdaacf", "input")

          val outputBytes = patchUserGroupInformationClass(inputBytes)
          ensureMatchingDigest(outputBytes, "md5:16a321b5a4ffa65946da39bccfc6883f", "output")

          storeJarEntry(jos, s"META-INF/versions/23/${entry.getName}", outputBytes)
        }
      }
    } match {
      case Failure(exception) =>
        log.error(s"Hadoop Client API patcher: ${exception.getMessage}")
        false
      case Success(value) => true
    }
  }

  private def createOrUpdateManifest(manifest: Option[Manifest]) = {
    val result = manifest.getOrElse(new Manifest)
    result.getMainAttributes().putValue("Multi-Release", "true")
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
      Option(jis.getNextJarEntry()).map(entry => Some(entry, jis)).getOrElse(None)
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

  private def storeJarEntry(jos: JarOutputStream, name: String, bytes: Array[Byte]): Unit = {
    jos.putNextEntry(new JarEntry(name))
    jos.write(bytes)
    jos.closeEntry
  }

  // ASM transformer classes.

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
    ) = {
      // Check if the method being called is Subject.getSubject
      if (isGetSubjectMethod(owner, name, descriptor)) {
        if (opcode != Opcodes.INVOKESTATIC) {
          throw new AssertionError(s"${owner}.${name} invocation is not static")
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

}
