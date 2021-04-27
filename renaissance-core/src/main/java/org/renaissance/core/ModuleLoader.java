package org.renaissance.core;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.lang.reflect.Constructor;
import java.net.MalformedURLException;
import java.net.URL;
import java.net.URLClassLoader;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Properties;
import java.util.Set;
import java.util.logging.Level;
import java.util.logging.Logger;
import java.util.stream.Stream;

import static java.util.Collections.emptyMap;
import static java.util.function.Function.identity;
import static java.util.stream.Collectors.joining;
import static java.util.stream.Collectors.toMap;

public final class ModuleLoader {
  private static final String RESOURCE_PATH_SEPARATOR = "/";

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
   */
  private final Map<String, Set<String>> jarPathsByModule;


  ModuleLoader(Path scratchRootDir, Map<String, Set<String>> jarPathsByModule) {
    this.scratchRootDir = scratchRootDir;
    this.jarPathsByModule = jarPathsByModule;
  }


  /**
   * Creates a module loader with a given scratch root directory. The module
   * loader loads a property file with a module description and allows loading
   * modules using independent class loaders.
   *
   * @param scratchRootDir The root of the scratch directory where module
   * module dependencies are extracted.
   */
  public static ModuleLoader create(Path scratchRootDir) {
    logger.fine(() -> String.format(
      "Creating module loader with scratch root '%s'", scratchRootDir
    ));

    String moduleProperties = resourceAbsolutePath("modules.properties");
    final Map<String, Set<String>> moduleJarPaths = loadModuleJarPaths(moduleProperties);
    return new ModuleLoader(scratchRootDir, moduleJarPaths);
  }


  /**
   * Loads the set of JAR resource paths for all modules from a property file.
   * This method should not throw any exception because it is used in a static
   * class initializer.
   *
   * @param resourceName the name of the resource to load.
   * @return A {@link Map} with the module name as the key and a {@link Set}
   * of JAR file paths as the value.
   */
  private static Map<String, Set<String>> loadModuleJarPaths(String resourceName) {
    logger.fine(() -> String.format (
      "Loading module JAR sets from resource '%s'", resourceName
    ));

    try (
      InputStream stream = ModuleLoader.class.getResourceAsStream(resourceName)
    ) {
      Map<String, Set<String>> result = loadModuleProperties(stream);

      if (logger.isLoggable(Level.CONFIG)) {
        logModuleJarPaths(result);
      }

      return result;

    } catch (IOException e) {
      // Fail gracefully with an empty collection.
      logger.severe("Failed to load module JAR paths: "+ e.getMessage());
      return emptyMap();
    }
  }


  private static Map<String, Set<String>> loadModuleProperties(InputStream stream)
  throws IOException {
    Properties props = new Properties();
    props.load(stream);

    return props.stringPropertyNames().stream().collect(toMap(
      identity(), name -> pathsToSet(props.getProperty(name))
    ));
  }


  private static Set<String> pathsToSet(String paths) {
    // Convert "path1/to/jar1,path2/to/jar2,..." into a set of paths.
    return new LinkedHashSet<>(Arrays.asList(paths.split(",")));
  }


  private static <T extends Collection<?>> void logModuleJarPaths(Map<String, T> result) {
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


  ClassLoader createClassLoaderForModule(String name) throws ModuleLoadingException {
    logger.fine(() -> String.format("Creating class loader for module '%s'", name));

    //
    // Look up the module name and create a directory for the module JAR files.
    // Extract the JAR files and build an URL classloader for the module. Reuse
    // the JAR files in the module directory (but create a new classloader) to
    // avoid repeatedly extracting the JAR files for the same module.
    //
    try {
      Set<String> jarPaths = jarPathsByModule.get(name);
      if (jarPaths == null) {
        throw new ModuleLoadingException("module not found");
      }

      Path moduleJarsDir = createModuleJarsDirectory(name);
      List<Path> filePaths = extractResources(jarPaths, moduleJarsDir);
      final URL[] urls = pathsToUrls(filePaths);

      // Make sure that all paths were converted to URL.
      if (urls.length != filePaths.size()) {
        throw new ModuleLoadingException("malformed URL(s) in module JAR paths");
      }

      logger.fine(() -> String.format(
        "Module '%s' class path (%d entries): %s",
        name, filePaths.size(), makeClassPath(filePaths)
      ));

      return new URLClassLoader(urls, thisClass.getClassLoader());

    } catch (IOException e) {
      throw new ModuleLoadingException(
        "error creating module jar directory: %s", e.getMessage()
      );
    }
  }


  private Path createModuleJarsDirectory(String name) throws IOException {
    // Create '<module-name>/lib' directory in scratch root.
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


  private static List<Path> extractResources(
    Collection<String> resourcePaths, Path outputDirPath
  ) throws ModuleLoadingException {
    List<Path> result = new ArrayList<>();

    for (String resourcePath : resourcePaths) {
      Path outputFilePath = outputDirPath.resolve(resourceFileName(resourcePath));
      logger.finer(() -> String.format(
        "Resource '%s' expected at '%s'", resourcePath, outputFilePath
      ));

      if (!Files.exists(outputFilePath)) {
        logger.finer(() -> String.format(
          "File '%s' does not exist, extracting resource", outputFilePath
        ));

        try {
          extractResource(resourcePath, outputFilePath);

        } catch (IOException e) {
          // Report the particular resource and target.
          throw new ModuleLoadingException(
            "could not extract resource '%s' into '%s': %s",
            resourcePath, outputFilePath, e.getMessage()
          );
        }

      } else {
        logger.finer(() -> String.format(
          "File '%s' already exists, skipping extraction", outputFilePath
        ));
      }

      result.add(outputFilePath);
    }

    return result;
  }


  private static String resourceAbsolutePath(String resourcePath) {
    return resourcePath.startsWith(RESOURCE_PATH_SEPARATOR)
      ? resourcePath : RESOURCE_PATH_SEPARATOR + resourcePath;
  }


  private static String resourceFileName(String resourcePath) {
    final int nameStart = resourcePath.lastIndexOf(RESOURCE_PATH_SEPARATOR);
    return nameStart >= 0 ? resourcePath.substring(nameStart + 1) : resourcePath;
  }


  private static void extractResource(String resourcePath, Path outputFilePath)
  throws IOException {
    final String absResourcePath = resourceAbsolutePath(resourcePath);

    try (
      InputStream resourceStream = thisClass.getResourceAsStream(absResourcePath)
    ) {
      if (resourceStream == null) {
        // This should only happen in case of build misconfiguration.
        throw new IOException("resource not found");
      }

      // Copy the stream contents to the file (without overwriting).
      long bytesWritten = Files.copy(resourceStream, outputFilePath);
      logger.finer(() -> String.format(
        "Wrote %d bytes to '%s'", bytesWritten, outputFilePath
      ));
    }
  }


  /**
   * Creates a factory which can create instances of (extension) classes. The
   * factory first tries to use a constructor which takes an array of strings as
   * a parameter and passes the given arguments array to that constructor. If
   * such a constructor cannot be found, it falls back to using the default
   * constructor.
   */
  public static <T> T createExtension(
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


  /**
   * Loads an extension class and casts it to the desired base class.
   * The class is searched for in the given class path.
   */
  public static <T> Class<? extends T> loadExtension(
    String classPath, String className, Class<T> baseClass
  ) throws ModuleLoadingException {
    String[] pathElements = classPath.split(File.pathSeparator);
    URL[] classPathUrls = stringsToUrls(pathElements);
    if (classPathUrls.length != pathElements.length) {
      throw new ModuleLoadingException("malformed URL(s) in classpath specification");
    }

    try {
      ClassLoader parent = ModuleLoader.class.getClassLoader();
      ClassLoader loader = new URLClassLoader(classPathUrls, parent);
      Class<?> loadedClass = loader.loadClass(className);
      return loadedClass.asSubclass(baseClass);

    } catch (ClassNotFoundException e) {
      // Be a bit more verbose, because the ClassNotFoundException
      // on OpenJDK only returns the class name as error message.
      throw new ModuleLoadingException(
        "could not find class '%s'", className
      );
    } catch (ClassCastException e) {
      throw new ModuleLoadingException(
        "class '%s' is not a subclass of '%s'", className, baseClass.getName()
      );
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

  private static URL[] pathsToUrls(Collection<Path> paths) {
    //
    // Because it is not possible to construct an URL from a relative file
    // path (which would be probably the most common scenario), we convert
    // the file path to an URI first and convert that to an URL.
    //
    return stringsToUrls(paths.stream().map(p -> p.toUri().toString()));
  }

  private static URL[] stringsToUrls(String[] strings) {
    return stringsToUrls(Arrays.stream(strings));
  }

  private static URL[] stringsToUrls(Stream<String> stringStream) {
    return stringStream.map(ModuleLoader::makeUrl).filter(Objects::nonNull).toArray(URL[]::new);
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

  public static final class ModuleLoadingException extends Exception {
    ModuleLoadingException(String message) {
      super(message);
    }

    ModuleLoadingException(String format, Object... args) {
      super(String.format(format, args));
    }
  }

}
