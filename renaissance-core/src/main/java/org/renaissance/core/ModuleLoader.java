package org.renaissance.core;

import java.io.File;
import java.io.IOException;
import java.lang.reflect.Constructor;
import java.net.MalformedURLException;
import java.net.URI;
import java.net.URL;
import java.net.URLClassLoader;
import java.nio.file.Path;
import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.logging.Level;
import java.util.logging.Logger;

import static java.util.Arrays.asList;
import static java.util.stream.Collectors.toMap;
import static org.renaissance.core.ResourceUtils.getMetadataUrl;
import static org.renaissance.core.ResourceUtils.loadPropertiesAsMap;

public final class ModuleLoader {

  private static final Class<?> thisClass = ModuleLoader.class;
  private static final Logger logger = Logging.getPackageLogger(thisClass);

  static {
    // Provide a handler that allows loading JAR files from resources.
    URL.setURLStreamHandlerFactory(ResourceUrlConnection.FACTORY);
  }

  /**
   * Map of module names to sets of JAR files representing the class path of
   * each module. There may be multiple benchmark classes in one module, but
   * each will be instantiated using a separate class loader.
   * <p>
   * Note: resource paths always use '/' as a path component separator.
   */
  private final Map<String, Set<String>> jarResourcePathsByModule;


  ModuleLoader(Map<String, Set<String>> jarPathsByModule) {
    this.jarResourcePathsByModule = jarPathsByModule;
  }


  /**
   * Creates a module loader. The module loader allows loading modules using
   * independent class loaders. Modules are defined in a property file and each
   * contains a list of JAR files representing a module-specific class path.
   *
   * @param moduleMetadataUri A {@link URI} pointing to a properties file
   * containing the list of JAR files for each module.
   */
  static ModuleLoader create(URI moduleMetadataUri) throws IOException {
    logger.fine(() -> String.format(
      "Creating module loader, moduleMetadata='%s'", moduleMetadataUri
    ));

    URL metadataUrl = getMetadataUrl(moduleMetadataUri);
    Map<String, String> properties = loadPropertiesAsMap(metadataUrl);
    Map<String, Set<String>> moduleJars = collectModuleJars(properties);

    if (logger.isLoggable(Level.CONFIG)) {
      logModuleJars(moduleJars);
    }

    return new ModuleLoader(moduleJars);
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


  ClassLoader createClassLoaderForModule(String name) throws ModuleLoadingException {
    logger.fine(() -> String.format("Creating class loader for module '%s'", name));

    //
    // Look up the module name and build an URLClassloader for the module,
    // referring to the JAR files using the 'resource:' prefix.
    //
    Set<String> jarResourcePaths = jarResourcePathsByModule.get(name);
    if (jarResourcePaths == null) {
      throw new ModuleLoadingException("module not found: %s", name);
    }

    final URL[] jarResourceUrls = resourcePathsToUrls(jarResourcePaths);

    // Make sure all paths were converted to URL.
    if (jarResourceUrls.length != jarResourcePaths.size()) {
      throw new ModuleLoadingException("malformed URL(s) in module JAR paths");
    }

    logger.fine(() -> String.format(
      "Module '%s' class path (%d entries): %s",
      name, jarResourceUrls.length, makeClassPath(jarResourcePaths)
    ));

    // Load module JARs from the resources.
    return new URLClassLoader(jarResourceUrls, thisClass.getClassLoader());
  }


  private static String makeClassPath(Collection<String> paths) {
    return String.join(File.pathSeparator, paths);
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
  // Because creating a URL instance can throw a (checked!) exception, which
  // Java streams are unable to handle, we suppress (but log) that exception
  // and return null instead, which we filter out.
  //
  // We can check later whether the conversion was complete or not and take a
  // summary action, knowing that individual conversion failures were logged.
  //

  static URL[] pathsToUrls(Collection<Path> paths) {
    //
    // Because it is impossible to construct a URL from a relative file
    // path (which would be probably the most common scenario), we convert
    // the file path to a URI first and convert that to a URL.
    //
    return paths.stream()
      .map(Path::toUri)
      .map(ModuleLoader::makeUrl)
      .filter(Objects::nonNull)
      .toArray(URL[]::new);
  }

  static URL[] resourcePathsToUrls(Collection<String> paths) {
    //
    // Add a protocol prefix to resource path to create a URI,
    // which can be then converted to a URL.
    //
    String uriPrefix = ResourceUrlConnection.PROTOCOL + ":/";
    return paths.stream()
      .map(rp -> URI.create(uriPrefix + rp))
      .map(ModuleLoader::makeUrl)
      .filter(Objects::nonNull)
      .toArray(URL[]::new);
  }

  private static URL makeUrl(URI uri) {
    try {
      // Avoid URL constructor deprecated since Java 20.
      return uri.toURL();
    } catch (MalformedURLException e) {
      logger.warning(String.format("Failed to convert '%s' to URL", uri));
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
