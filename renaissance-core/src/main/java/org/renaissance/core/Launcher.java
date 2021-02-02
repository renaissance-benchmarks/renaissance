package org.renaissance.core;

import org.renaissance.Benchmark;
import org.renaissance.core.ModuleLoader.ModuleLoadingException;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.logging.Logger;

import static org.renaissance.core.ModuleLoader.createClassLoaderForModule;

public final class Launcher {
  private static final String MARKDOWN_GENERATOR = "org.renaissance.harness.MarkdownGenerator";
  private static final String RENAISSANCE_SUITE = "org.renaissance.harness.RenaissanceSuite";
  private static final Logger logger = Logging.getPackageLogger(Launcher.class);

  /**
   * The root of the scratch directory.
   *
   * TODO Move into harness-wide context.
   */
  static Path scratchRootDir;

  public static void main(String[] args) {
    if (args.length == 1 && "--readme".equalsIgnoreCase(args[0])) {
      final Package benchmarkPkg = Benchmark.class.getPackage();
      final String[] generatorArgs = new String[] {
        "--title", benchmarkPkg.getSpecificationTitle(),
        "--version", benchmarkPkg.getImplementationVersion()
      };

      // TODO Launch the generator from the build system.
      System.exit(launchHarnessClass(MARKDOWN_GENERATOR, generatorArgs));
    } else {
      System.exit(launchHarnessClass(RENAISSANCE_SUITE, args));
    }
  }


  private static int launchHarnessClass(String className, String[] args) {
    try {
      Path scratchBaseDir = Paths.get(System.getProperty("java.io.tmpdir", "."));
      logger.fine(() -> "Creating scratch directory in: "+ scratchBaseDir);
      scratchRootDir = Files.createTempDirectory(scratchBaseDir, "renaissance-");

      // The scratch root MUST be initialized at this point.
      logger.config(() -> "Scratch directory root: " + scratchRootDir);
      return loadAndInvokeHarnessClass(className, args);

    } catch (IOException e) {
      logger.severe(prefixStackTrace("Failed to create scratch directory: ", e));
      return 1;

    } finally {
      logger.fine("Deleting scratch directory: " + scratchRootDir);
      DirUtils.deleteTempDir(scratchRootDir);
    }
  }


  private static int loadAndInvokeHarnessClass(String className, String[] args) {
    try {
      ClassLoader loader = createClassLoaderForModule("renaissance-harness");
      Class<?> suiteClass = loader.loadClass(className);
      Method suiteMain = suiteClass.getMethod("main", String[].class);
      suiteMain.invoke(null, new Object[] { args });
      return 0;

    } catch (ModuleLoadingException e) {
      logger.severe(prefixStackTrace("Failed to load harness: ", e));
    } catch (InvocationTargetException e) {
      // Catch this before the more general ReflectiveOperationException.
      logger.severe(prefixStackTrace("Harness failed with ", e.getCause()));
    } catch (ReflectiveOperationException e) {
      logger.severe(prefixStackTrace("Failed to initialize harness: ", e));
    }

    return 1;
  }


  private static String prefixStackTrace(final String prefix, Throwable cause) {
    final ByteArrayOutputStream bytes = new ByteArrayOutputStream();
    final PrintStream printer = new PrintStream(bytes);

    printer.append(prefix);
    cause.printStackTrace(printer);
    printer.close();

    return bytes.toString();
  }

}
