package org.renaissance.core;

import org.renaissance.Plugin;

import java.io.*;
import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.net.MalformedURLException;
import java.net.URL;
import java.net.URLClassLoader;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.*;
import java.util.function.Function;
import java.util.logging.Logger;

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


  public static Plugin loadPlugin(
    String classPath, String className
  ) throws ModuleLoadingException {
    try {
      Class<? extends Plugin> pluginClass = loadExternalClass(classPath, className, Plugin.class);
      Constructor<? extends Plugin> pluginCtor = pluginClass.getDeclaredConstructor();
      return pluginCtor.newInstance();

    } catch (ReflectiveOperationException e) {
      throw new ModuleLoadingException(String.format(
        "could not instantiate plugin %s: %s", className, e.getMessage()
      ));
    }
  }

  public static <T> Class<? extends T> loadExternalClass(
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
      // Be a bit more verbose, the ClassNotFoundException on OpenJDK
      // only returns the class name as error message.
      throw new ModuleLoadingException(String.format(
        "could not find class '%s'", className
      ));
    } catch (ClassCastException e) {
      throw new ModuleLoadingException(String.format(
        "class '%s' is not a subclass of '%s'", className, baseClass.getName()
      ));
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

  private static URL[] stringsToUrls(String[] urls) {
    Logger logger = Logging.getMethodLogger(ModuleLoader.class, "stringsToUrls");

    //
    // What we do here is actually quite simple:
    //
    //    urls.map(p -> new URL(path)).toArray()
    //
    // However, URL instantiation can throw (checked!) exception which Java
    // streams are unable to handle. So we suppress that exception and return
    // null instead, which we later filter out. This allows us to later check
    // whether exception was thrown and artificially re-throw it.
    //
    // Next surprise is that it is not possible to construct an URL from a
    // relative file path (which would be probably the most common scenario)
    // so we first try a full-fledged URL and then a filepath URI.
    //
    Function<String, URL> makeUrl = path -> {
      try {
        return Paths.get(path).toUri().toURL();
      } catch (MalformedURLException e) {
        logger.severe(String.format("Ignoring malformed URL '%s'", path));
        return null;
      }
    };

    return Arrays.stream(urls)
      .map(makeUrl)
      .filter(Objects::nonNull)
      .toArray(URL[]::new);
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
