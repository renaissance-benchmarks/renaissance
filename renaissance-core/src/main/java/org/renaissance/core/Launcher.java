package org.renaissance.core;

import org.renaissance.Benchmark;
import org.renaissance.core.ModuleLoader.ModuleLoadingException;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.net.URI;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Optional;
import java.util.function.Predicate;
import java.util.logging.Logger;

import static org.renaissance.core.DirUtils.createScratchDirectory;

public final class Launcher {
  private static final Logger logger = Logging.getPackageLogger(Launcher.class);

  private static final String MARKDOWN_GENERATOR = "org.renaissance.harness.MarkdownGenerator";
  private static final String HARNESS_MAIN_CLASS = "org.renaissance.harness.RenaissanceSuite";
  private static final String HARNESS_MODULE_NAME = "renaissance-harness_3";

  private static final URI moduleMetadataUri = URI.create("resource:/modules.properties");


  public static void main(String[] args) {
    try {
      if (args.length == 1 && "--readme".equalsIgnoreCase(args[0])) {
        final Package benchmarkPkg = Benchmark.class.getPackage();
        final String fullVersion = benchmarkPkg.getImplementationVersion();
        final String[] generatorArgs = new String[] {
          "--title", benchmarkPkg.getSpecificationTitle(),
          "--version", fullVersion.split("-")[0]
        };

        // TODO Launch the generator from the build system.
        launchHarnessClass(MARKDOWN_GENERATOR, generatorArgs);
      } else {
        launchHarnessClass(HARNESS_MAIN_CLASS, args);
      }

    } catch (LaunchException e) {
      logger.severe(prefixStackTrace(
        e.getMessage(), Optional.of(e.getCause())
      ));

      System.err.println(e.getMessage());
      System.exit(1);
    }
  }


  private static void launchHarnessClass(
    String className, String[] args
  ) throws LaunchException {
    //
    // Determine the launcher scratch base directory, in which to create the
    // actual scratch directory. By default, we use the current directory as
    // the scratch base, even though it may seem tempting to put it in the
    // system temporary directory. However, temporary directory (on Linux) is
    // often backed by "tmpfs" file system and storing data there may create
    // artificial memory pressure, causing the system to swap other things
    // out and impact the results.
    //
    Path scratchBaseDir = getScratchBase(args);
    logger.config(() -> "Scratch base: "+ printable(scratchBaseDir));

    Path scratchRootDir = createScratchRoot(scratchBaseDir, getKeepScratch(args));
    logger.config(() -> "Scratch root (launcher): " + printable(scratchRootDir));

    // Create module loader with launcher-specific scratch root.
    try {
      ModuleLoader loader = ModuleLoader.create(scratchRootDir, moduleMetadataUri);
      loadAndInvokeHarnessClass(loader, className, args);

    } catch (IOException e) {
      throw new LaunchException(e, "failed to create module loader");
    }
  }

  private static Path createScratchRoot(
    Path scratchBaseDir, boolean keepScratch
  ) throws LaunchException {
    try {
      return createScratchDirectory(scratchBaseDir, "launcher-", keepScratch);
    } catch (IOException e) {
      throw new LaunchException(e, "failed to create scratch directory");
    }
  }

  private static Path printable(Path path) {
    return path.toAbsolutePath().normalize();
  }

  private static Path getScratchBase(String[] args) throws LaunchException {
    // The '--scratch-base' option needs to be kept in sync with the harness.
    final Optional<Integer> optIndex = arrayIndexOf(args, "--scratch-base"::equalsIgnoreCase);

    if (optIndex.isPresent()) {
      int valIndex = optIndex.get() + 1;
      if (valIndex >= args.length) {
        throw new LaunchException("Missing directory after --scratch-base option!");
      }

      return Paths.get(args[valIndex]);
    } else {
      return Paths.get("");
    }
  }


  private static boolean getKeepScratch(String[] args) {
    // The '--keep-scratch' option needs to be kept in sync with the harness.
    return arrayIndexOf(args, "--keep-scratch"::equalsIgnoreCase).isPresent();
  }


  private static void loadAndInvokeHarnessClass(
    ModuleLoader loader, String className, String[] args
  ) throws LaunchException {
    try {
      ClassLoader classLoader = loader.createClassLoaderForModule(HARNESS_MODULE_NAME);
      Class<?> suiteClass = classLoader.loadClass(className);
      Method suiteMain = suiteClass.getMethod("main", String[].class);
      suiteMain.invoke(null, new Object[] { args });

    } catch (ModuleLoadingException e) {
      throw new LaunchException(e, "Failed to load harness: ");
    } catch (InvocationTargetException e) {
      // Catch this before the more general ReflectiveOperationException.
      throw new LaunchException(e.getCause(), "Harness failed with ");
    } catch (ReflectiveOperationException e) {
      throw new LaunchException(e, "Failed to initialize harness: ");
    }
  }


  private static <T> Optional<Integer> arrayIndexOf(T[] array, Predicate<T> matcher) {
    for (int index = 0; index < array.length; index++) {
      if (matcher.test(array[index])) {
        return Optional.of(index);
      }
    }

    return Optional.empty();
  }


  private static String prefixStackTrace(final CharSequence prefix, Optional<Throwable> optionalCause) {
    final ByteArrayOutputStream bytes = new ByteArrayOutputStream();

    final PrintStream printer = new PrintStream(bytes);
    printer.append(prefix);
    optionalCause.ifPresent(cause -> cause.printStackTrace(printer));
    printer.close();

    return bytes.toString();
  }


  private static final class LaunchException extends Exception {
    LaunchException(String message) {
      super(message);
    }

    LaunchException(Throwable cause, String message) {
      super(message, cause);
    }
  }

}
