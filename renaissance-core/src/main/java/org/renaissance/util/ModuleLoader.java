package org.renaissance.util;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.net.URL;
import java.net.URLClassLoader;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Scanner;
import java.util.logging.Logger;

import org.renaissance.Launcher;

public class ModuleLoader {
  private static final URL[] URL_ARRAY_TYPE = new URL[0];

  private static final Map<String, String[]> GROUP_JAR_NAMES
    = getGroupJarNames(ModuleLoader.class.getResourceAsStream("/groups-jars.txt"));

  public static ClassLoader getForGroup(String groupName) throws ModuleLoadingException {
    Logger logger = Logging.getMethodLogger(ModuleLoader.class, "getGroupClassloader");

    String[] jarNames = GROUP_JAR_NAMES.get(groupName);
    if (jarNames == null) {
      String message = String.format("Group %s not found", groupName);
      throw new ModuleLoadingException(message);
    }

    List<InputStream> jarStreams = new ArrayList<>();
    for (String path : jarNames) {
      jarStreams.add(Launcher.class.getResourceAsStream("/" + path));
    }

    try {
      ClassLoader parent = ModuleLoader.class.getClassLoader();
      URL[] extractedUrls = extractAndGetUrls(jarStreams);
      for (InputStream is : jarStreams) {
        is.close();
      }

      return new URLClassLoader(extractedUrls, parent);
    } catch (IOException e) {
      String message = String.format("Failed to load %s: %s", groupName, e.getMessage());
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
      String parts[] = line.split("=");
      if (parts.length != 2) {
        continue;
      }
      String group = parts[0];
      String jars[] = parts[1].split(",");
      result.put(group, jars);

      logger.finest(String.format("Found group entry %s => %s (%d)", group, parts[1], jars.length));
    }
    sc.close();

    return result;
  }

  private static URL[] extractAndGetUrls(List<InputStream> streams) throws IOException {
    Logger logger = Logging.getMethodLogger(ModuleLoader.class, "extractAndGetUrls");

    Path baseDir = Paths.get(".");
    Path baseUnpackDir = Files.createTempDirectory(baseDir, "tmp-jars-");
    baseUnpackDir.toFile().deleteOnExit();
    List<URL> resultUrls = new ArrayList<>();

    for (InputStream inputJar : streams) {
      Path unpackedTargetPath = Files.createTempFile(baseUnpackDir, "cp-", ".jar");
      File unpackedTarget = unpackedTargetPath.toFile();
      unpackedTarget.deleteOnExit();
      OutputStream unpackedOutStream = new FileOutputStream(unpackedTarget);

      logger.fine(String.format("Extracting %s into %s", inputJar, unpackedTargetPath));

      byte[] buffer = new byte[8 * 1024];
      int bytesRead;
      while ((bytesRead = inputJar.read(buffer)) != -1) {
        unpackedOutStream.write(buffer, 0, bytesRead);
      }

      unpackedOutStream.close();

      resultUrls.add(unpackedTargetPath.toUri().toURL());
    }

    return resultUrls.toArray(URL_ARRAY_TYPE);
  }
}
