package org.renaissance.core;

import java.io.*;
import java.net.MalformedURLException;
import java.net.URL;
import java.net.URLClassLoader;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.*;
import java.util.logging.Logger;
import java.util.stream.Collectors;

import org.renaissance.Plugin;

public final class ModuleLoader {
  private static final URL[] URL_ARRAY_TYPE = new URL[0];

  private static final Map<String, String[]> GROUP_JAR_NAMES
    = getGroupJarNames(ModuleLoader.class.getResourceAsStream("/groups-jars.txt"));

  static ClassLoader getForGroup(String groupName) throws ModuleLoadingException {
    Logger logger = Logging.getMethodLogger(ModuleLoader.class, "getGroupClassloader");

    String[] jarNames = GROUP_JAR_NAMES.get(groupName);
    if (jarNames == null) {
      String message = String.format("Group %s not found", groupName);
      throw new ModuleLoadingException(message);
    }

    List<Pair<String, InputStream>> jarStreams = new ArrayList<>();
    for (String path : jarNames) {
      jarStreams.add(new Pair<>(path, Launcher.class.getResourceAsStream("/" + path)));
    }

    try {
      ClassLoader parent = ModuleLoader.class.getClassLoader();
      URL[] extractedUrls = extractAndGetUrls(jarStreams);
      for (Pair<String, InputStream> stream: jarStreams) {
        stream.second().close();
      }

      return new URLClassLoader(extractedUrls, parent);
    } catch (IOException e) {
      String message = String.format("Failed to load %s: %s", groupName, e.getMessage());
      logger.severe(message);
      throw new ModuleLoadingException(message, e);
    }
  }

  public static Plugin loadPlugin(String spec) throws ModuleLoadingException {
    Logger logger = Logging.getMethodLogger(ModuleLoader.class, "loadPlugin");
    String[] parts = spec.split("!");
    if (parts.length != 2) {
      String message = "Plugin loading failed: expecting classpath!classname format.";
      logger.severe(message);
      throw new ModuleLoadingException(message);
    }
    String[] classpath = parts[0].split(File.pathSeparator);
    String classname = parts[1];

    /*
     * Note that we do not use multicatch as some exceptions gives very
     * little information about their cause (e.g. ClassNotFoundException
     * on OpenJDK contains only the class name).
     */
    try {
      URL[] classpathUrls = stringsToUrls(classpath);
      ClassLoader parent = ModuleLoader.class.getClassLoader();
      ClassLoader loader = new URLClassLoader(classpathUrls, parent);
      Class<?> pluginClass = loader.loadClass(classname);
      Object pluginObj = pluginClass.newInstance();
      return (Plugin) pluginObj;
    } catch (MalformedURLException e) {
      String message = String.format("Plugin loading failed: %s.", e.getMessage());
      logger.severe(message);
      throw new ModuleLoadingException(message, e);
    } catch (ClassNotFoundException e) {
      String message = String.format("Plugin loading failed: unable to load %s (%s).", classname, e.getMessage());
      logger.severe(message);
      throw new ModuleLoadingException(message, e);
    } catch (InstantiationException | IllegalAccessException e) {
      String message = String.format("Plugin loading failed: unable to instantiate %s (%s).", classname, e.getMessage());
      logger.severe(message);
      throw new ModuleLoadingException(message, e);
    }
  }
  
  private static Map<String, String[]> getGroupJarNames(InputStream jarList) {
    Logger logger = Logging.getMethodLogger(ModuleLoader.class, "getGroupJarNames");

    if (jarList == null) {
      logger.severe("JAR list stream is null.");
      return new HashMap<>();
    }

    Scanner sc = new Scanner(jarList);
    Map<String, String[]> result = new HashMap<>();
    while (sc.hasNextLine()) {
      String line = sc.nextLine();
      String[] parts = line.split("=");
      if (parts.length != 2) {
        continue;
      }
      String group = parts[0];
      String[] jars = parts[1].split(",");
      result.put(group, jars);

      logger.finest(String.format("Found group entry %s => %s (%d)", group, parts[1], jars.length));
    }
    sc.close();

    return result;
  }

  private static URL[] extractAndGetUrls(List<Pair<String, InputStream>> streams) throws IOException {
    Logger logger = Logging.getMethodLogger(ModuleLoader.class, "extractAndGetUrls");

    Path baseDir = Paths.get(".");
    Path baseUnpackDir = Files.createTempDirectory(baseDir, "tmp-jars-");
    baseUnpackDir.toFile().deleteOnExit();
    List<URL> resultUrls = new ArrayList<>();

    for (Pair<String, InputStream> stream : streams) {
      String path = stream.first();
      String name = new File(path).getName();
      InputStream is = stream.second();
      Path unpackedTargetPath = Files.createTempFile(baseUnpackDir, "cp-" + name, ".jar");
      File unpackedTarget = unpackedTargetPath.toFile();
      unpackedTarget.deleteOnExit();
      OutputStream unpackedOutStream = new FileOutputStream(unpackedTarget);

      logger.fine(String.format("Extracting %s into %s", is, unpackedTargetPath));

      byte[] buffer = new byte[8 * 1024];
      int bytesRead;
      while ((bytesRead = is.read(buffer)) != -1) {
        unpackedOutStream.write(buffer, 0, bytesRead);
      }

      unpackedOutStream.close();

      resultUrls.add(unpackedTargetPath.toUri().toURL());
    }

    return resultUrls.toArray(URL_ARRAY_TYPE);
  }

  private static URL[] stringsToUrls(String[] urls) throws MalformedURLException {
    Logger logger = Logging.getMethodLogger(ModuleLoader.class, "stringsToUrls");

    /*
     * What we do here is actually quite simple:
     *
     *   urls.map(p -> new URL(path)).toArray()
     *
     * However, URL instantiation can throw (checked!) exception that Java
     * streams are unable to handle. So we surpress that exception and return
     * null instead that we later filter out. This allows us to later check
     * whether exception was thrown and artificially re-throw it.
     *
     * Next surprise is that it is not possible to construct URL from
     * relative file path (which would be probably the most common scenario)
     * so we first try full-fledged URL and then filepath URI.
     */
    URL[] result = Arrays.stream(urls)
      .map(path -> {
        try {
          return new URL(path);
        } catch (MalformedURLException e) {
          try {
            return Paths.get(path).toUri().toURL();
          } catch (MalformedURLException e2) {
            logger.severe(String.format("Ignoring malformed URL %s.", path));
            return null;
          }
        }
      }).filter(url -> url != null)
      .toArray(URL[]::new);
    if (result.length != urls.length) {
      throw new MalformedURLException(String.format("Some URLs in %s are malformed.", String.join(File.pathSeparator, urls)));
    }
    return result;
  }

  //

  public static final class ModuleLoadingException extends Exception {

    ModuleLoadingException(String message) {
      super(message);
    }

    ModuleLoadingException(String message, Throwable cause) {
      super(message, cause);
    }

  }

}
