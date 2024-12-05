package org.renaissance.core;

import java.io.File;
import java.io.IOException;
import java.lang.reflect.Constructor;
import java.net.MalformedURLException;
import java.net.URI;
import java.net.URL;
import java.net.URLClassLoader;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Objects;
import java.util.Set;
import java.util.logging.Level;
import java.util.logging.Logger;

import static java.util.Arrays.asList;
import static java.util.stream.Collectors.joining;
import static java.util.stream.Collectors.toMap;
import static org.renaissance.core.ResourceUtils.extractResources;
import static org.renaissance.core.ResourceUtils.getMetadataUrl;
import static org.renaissance.core.ResourceUtils.loadPropertiesAsMap;

public final class ModuleLoader {

  private static final Class<?> thisClass = ModuleLoader.class;
  private static final Logger logger = Logging.getPackageLogger(thisClass);


  /**
   * The root of the scratch directory for this module loader.
   */
  private final Path scratchRootDir;

  /**
   * Map of module names to sets of JAR files representing the class path of
   * each module. There may be multiple benchmark classes in one module, but
   * each will be instantiated using a separate class loader.
   *
   * The resource paths use a Unix-style component separator.
   */
  private final Map<String, Set<String>> jarResourcePathsByModule;


  ModuleLoader(Path scratchRootDir, Map<String, Set<String>> jarPathsByModule) {
    this.scratchRootDir = scratchRootDir;
    this.jarResourcePathsByModule = jarPathsByModule;
  }


  /**
   * Creates a module loader with a given scratch root directory. The module
   * loader allows loading modules using independent class loaders. Modules
   * are defined in a property file and each contains a list of JAR files
   * representing a module-specific class path.
   *
   * @param scratchRootDir The root of the scratch directory into which
   * module dependencies get extracted.
   * @param moduleMetadataUri A {@link URI} pointing to a properties file
   * containing the list of JAR files for each module.
   */
  static ModuleLoader create(
    Path scratchRootDir, URI moduleMetadataUri
  ) throws IOException {
    logger.fine(() -> String.format(
      "Creating module loader, scratchRootDir='%s', moduleMetadata='%s'",
      scratchRootDir, moduleMetadataUri
    ));

    URL metadataUrl = getMetadataUrl(moduleMetadataUri);
    Map<String, String> properties = loadPropertiesAsMap(metadataUrl);
    Map<String, Set<String>> moduleJars = collectModuleJars(properties);

    if (logger.isLoggable(Level.CONFIG)) {
      logModuleJars(moduleJars);
    }

    return new ModuleLoader(scratchRootDir, moduleJars);
  }

  private static Map<String, Set<String>> collectModuleJars(Map<String, String> properties) {
    return properties.entrySet().stream()
      .collect(toMap(Map.Entry::getKey, entry -> pathsToSet(entry.getValue())));
  }

  private static Set<String> pathsToSet(String paths) {
    // Convert "path1/to/jar1,path2/to/jar2,..." into a set of paths.
    return new LinkedHashSet<>(asList(paths.split(",")));
  }


  private static <T extends Collection<?>> void logModuleJars(Map<String, T> result) {
    logger.config(String.format(
      "Found %d modules: %s", result.size(), result.keySet()
    ));

    result.forEach((group, jars) -> {
      logger.fine(String.format(
        "Module '%s' refers to %d files", group, jars.size()
      ));

      logger.finer(String.format(
        "JAR files for module '%s' => %s", group, jars
      ));
    });
  }


  /**
   * Extracts the given module to the given directory. Both the module and
   * the destination directory are expected to exist.
   */
  List<Path> extractModule(String name, Path dest) throws IOException {
    logger.fine(() -> String.format("Extracting module '%s' to %s", name, dest));

    Set<String> jarResourcePaths = jarResourcePathsByModule.get(name);
    if (jarResourcePaths != null) {
      return extractResources(jarResourcePaths, dest);
    } else {
      // Not supposed to happen, the caller should use the right module.
      throw new NoSuchElementException("there is no such module: "+ name);
    }
  }

  ClassLoader createClassLoaderForModule(String name) throws ModuleLoadingException {
    logger.fine(() -> String.format("Creating class loader for module '%s'", name));

    //
    // Look up the module name and create a directory for the module JAR files.
    // Extract the JAR files and build an URL classloader for the module. Reuse
    // the JAR files in the module directory (but create a new classloader) to
    // avoid repeatedly extracting the JAR files for the same module.
    //
    if (!jarResourcePathsByModule.containsKey(name)) {
      throw new ModuleLoadingException("module not found: %s", name);
    }

    try {
      Path moduleJarsDir = createModuleJarsDirectory(name);
      Set<String> jarResourcePaths = jarResourcePathsByModule.get(name);

      try {
        List<Path> filePaths = extractResources(jarResourcePaths, moduleJarsDir);
        final URL[] urls = pathsToUrls(filePaths);

        // Make sure all paths were converted to URL.
        if (urls.length != filePaths.size()) {
          throw new ModuleLoadingException("malformed URL(s) in module JAR paths");
        }

        logger.fine(() -> String.format(
          "Module '%s' class path (%d entries): %s",
          name, filePaths.size(), makeClassPath(filePaths)
        ));

        //
        // Make sure to explicitly close this URLClassLoader on exit, because it operates
        // on files created by the harness in the scratch directory hierarchy that need to
        // be deleted on exit. Leaving the class loader open keeps the library JAR files
        // open, preventing removal of the scratch directories. This is because on NFS,
        // deleting an open file produces a NFS temporary file in the same directory, and
        // on Windows, an open file cannot be deleted at all.
        //
        return Cleaner.closeOnExit(new URLClassLoader(urls, thisClass.getClassLoader()));

      } catch (IOException e) {
        // Just wrap the underlying IOException.
        throw new ModuleLoadingException(e.getMessage(), e);
      }

    } catch (IOException e) {
      throw new ModuleLoadingException(
        "error creating module jar directory: %s", e.getMessage()
      );
    }
  }


  private Path createModuleJarsDirectory(String name) throws IOException {
    // Put module jars into '<scratch-root>/<module-name>/lib' directory.
    Path result = Files.createDirectories(
      scratchRootDir.resolve(name).resolve("lib")
    );

    logger.config(String.format(
      "Module '%s' library directory: '%s'", name, result
    ));

    return result;
  }


  private static String makeClassPath(Collection<Path> paths) {
    return paths.stream().map(Path::toString).collect(joining(File.pathSeparator));
  }


  /**
   * Creates a factory which can create instances of (extension) classes. The
   * factory first tries to use a constructor which takes an array of strings as
   * a parameter and passes the given arguments array to that constructor. If
   * such a constructor cannot be found, it falls back to using the default
   * constructor.
   */
  static <T> T createExtension(
    Class<T> extClass, String[] args
  ) throws ModuleLoadingException {
    try {
      return newExtensionInstance(extClass, args);

    } catch (NoSuchMethodException e) {
      // Every class should have a default constructor.
      throw new ModuleLoadingException(
        "cannot find default constructor in '%s'", extClass.getName()
      );
    } catch (ReflectiveOperationException e) {
      throw new ModuleLoadingException(
        "cannot instantiate '%s': %s", extClass.getName(), e.getMessage()
      );
    }
  }

  private static <T> T newExtensionInstance(Class<T> extClass, String[] args)
  throws ReflectiveOperationException {
    try {
      // Try the constructor with parameters first.
      Constructor<T> ctor = extClass.getDeclaredConstructor(String[].class);
      return ctor.newInstance(new Object[] { args });

    } catch (NoSuchMethodException e) {
      // Fall back to default constructor.
      return extClass.getDeclaredConstructor().newInstance();
    }
  }


  //
  // Utility methods to convert things to an array of URLs.
  //
  // Because creating an URL instance can throw a (checked!) exception which
  // Java streams are unable to handle, we suppress (but log) that exception
  // and return null instead, which we filter out.
  //
  // We can check later whether the conversion was complete or not and take a
  // summary action, knowing that individual conversion failures were logged.
  //

  static URL[] pathsToUrls(Collection<Path> paths) {
    //
    // Because it is not possible to construct an URL from a relative file
    // path (which would be probably the most common scenario), we convert
    // the file path to an URI first and convert that to an URL.
    //
    return paths.stream()
      .map(p -> p.toUri().toString())
      .map(ModuleLoader::makeUrl)
      .filter(Objects::nonNull)
      .toArray(URL[]::new);
  }

  private static URL makeUrl(String spec) {
    try {
      return new URL(spec);
    } catch (MalformedURLException e) {
      logger.warning(String.format("Failed to convert '%s' to URL", spec));
      return null;
    }
  }

  //

  static final class ModuleLoadingException extends Exception {
    ModuleLoadingException(String message) {
      super(message);
    }

    ModuleLoadingException(String format, Object... args) {
      super(String.format(format, args));
    }
  }

}
