package org.renaissance.core;

import java.io.IOException;
import java.io.InputStream;
import java.net.MalformedURLException;
import java.net.URI;
import java.net.URL;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Enumeration;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Properties;
import java.util.jar.JarFile;
import java.util.jar.Manifest;
import java.util.logging.Logger;

import static java.util.function.Function.identity;
import static java.util.stream.Collectors.toMap;

public final class ResourceUtils {
  
  private static final Class<?> thisClass = ResourceUtils.class;
  private static final Logger logger = Logging.getPackageLogger(thisClass);

  private static final String RESOURCE_PATH_SEPARATOR = "/";

  static List<Path> extractResources(
    Iterable<String> resourcePaths, Path outputDirPath
  ) throws IOException {
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
          String message = String.format(
            "could not extract resource '%s' into '%s': %s",
            resourcePath, outputFilePath, e.getMessage()
          );

          throw new IOException(message, e);
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
  
  private static String resourceAbsolutePath(String resourcePath) {
    return resourcePath.startsWith(RESOURCE_PATH_SEPARATOR)
      ? resourcePath : RESOURCE_PATH_SEPARATOR + resourcePath;
  }

  /** Returns the last component of a resource path (base name). */
  static String resourceFileName(String resourcePath) {
    int nameStart = resourcePath.lastIndexOf(RESOURCE_PATH_SEPARATOR);
    return nameStart >= 0 ? resourcePath.substring(nameStart + 1) : resourcePath;
  }

  /**
   * Converts the given {@link URI} to a {@link URL}.
   * <p>If the {@link URI} scheme is {@code null}, the URI path is interpreted
   * as a file system {@link Path}, which is then converted to {@link URL}.
   * <p>If the {@link URI} scheme is 'resource', the scheme-specific part is
   * interpreted as a resource path with respect to this class.
   *
   * @param uri The {@link URI} to convert.
   * @return The {@link URL} corresponding to the given {@link URI}.
   * @throws IOException If the URI cannot be converted to {@link URL}
   */
  static URL getMetadataUrl(URI uri) throws IOException {
    //
    // Convert the URI to a URL. If the URI has a 'resource' scheme,
    // interpret it as a resource path with respect to this class.
    //
    String scheme = uri.getScheme();
    if (scheme == null) {
      return Paths.get(uri.getPath()).toUri().toURL();

    } else if ("resource".equalsIgnoreCase(scheme)) {
      String ssp = uri.getSchemeSpecificPart();
      URL result = ResourceUtils.class.getResource(ssp);
      if (result == null) {
        throw new IOException("cannot find resource with benchmark metadata: " + ssp);
      }

      return result;

    } else {
      try {
        return uri.toURL();

      } catch (MalformedURLException e) {
        throw new IOException(String.format(
          "cannot convert '%s' to URL: %s", uri, e.getMessage()
        ));
      }
    }
  }

  static Map<String, String> loadPropertiesAsMap(URL url) throws IOException {
    return toStringMap(loadProperties(url));
  }

  private static Map<String, String> toStringMap(Properties properties) {
    return properties.stringPropertyNames().stream()
      .collect(toMap(identity(), properties::getProperty));
  }

  static Properties loadProperties(URL url) throws IOException {
    try (
      // Auto-close the stream after finishing.
      final InputStream stream = url.openStream()
    ) {
      final Properties properties = new Properties();
      properties.load(stream);
      return properties;

    } catch (IOException e) {
      throw new IOException(String.format(
        "cannot load properties from '%s': %s", url, e.getMessage()
      ));
    }
  }

  /**
   * Read all manifests and find the first with the given property.
   * @returns Property value or {@code null} if not found.
   */
  public static Optional<String> getManifestAttributeValue(ClassLoader loader, String name) {
    try {
      Enumeration<URL> manifests = loader.getResources(JarFile.MANIFEST_NAME);
      while (manifests.hasMoreElements()) {
        URL manifestUrl = manifests.nextElement();
        try (
          // Close the stream automatically.
          InputStream mis = manifestUrl.openStream();
        ) {
          Manifest manifest = new Manifest(mis);
          String value = manifest.getMainAttributes().getValue(name);
          if (value != null) {
            return Optional.of(value);
          }

          // Try next manifest.
        } catch (IOException e) {
          // Try next manifest.
        }
      }
    } catch (IOException e) {
      // Could not find the attribute.
    }

    return Optional.empty();
  }

}
