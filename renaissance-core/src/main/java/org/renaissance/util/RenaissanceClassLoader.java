package org.renaissance.util;

import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Scanner;
import java.util.logging.Logger;

import org.renaissance.Launcher;

public class RenaissanceClassLoader {

  private static final Map<String, String[]> GROUP_JAR_NAMES
    = getGroupJarNames(RenaissanceClassLoader.class.getResourceAsStream("/groups-jars.txt"));

  public static ClassLoader getForGroup(String groupName) throws ClassNotFoundException {
    Logger logger = Logging.getMethodLogger(RenaissanceClassLoader.class, "getGroupClassloader");

    String[] jarNames = GROUP_JAR_NAMES.get(groupName);
    if (jarNames == null) {
      String message = String.format("Group %s not found", groupName);
      throw new ClassNotFoundException(message);
    }

    List<InputStream> jarStreams = new ArrayList<>();
    for (String path : jarNames) {
      jarStreams.add(Launcher.class.getResourceAsStream("/" + path));
    }

    try {
      ClassLoader parent = RenaissanceClassLoader.class.getClassLoader();
      ClassLoader result = new InputStreamClassLoader(parent, jarStreams.toArray(new InputStream[0]));
      for (InputStream is : jarStreams) {
        is.close();
      }
      return result;
    } catch (IOException e) {
      String message = String.format("Failed to load %s: %s", groupName, e.getMessage());
      logger.severe(message);
      throw new ClassNotFoundException(message, e);
    }
  }
  
  private static Map<String, String[]> getGroupJarNames(InputStream jarList) {
    Logger logger = Logging.getMethodLogger(RenaissanceClassLoader.class, "getGroupJarNames");

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
}
