package org.renaissance;

import java.lang.reflect.Method;
import java.util.logging.Logger;

import org.renaissance.util.Logging;
import org.renaissance.util.ModuleLoader;

public class Launcher {
  public static void main(String args[]) throws ClassNotFoundException {
    Logger logger = Logging.getMethodLogger(Launcher.class, "main");

    ClassLoader loader = ModuleLoader.getForGroup("renaissance-harness");

    try {
      Class<?> suiteClass = loader.loadClass("org.renaissance.RenaissanceSuite");
      Method suiteMain = suiteClass.getMethod("main", String[].class);
      suiteMain.invoke(null, new Object[] { args });
    } catch (ReflectiveOperationException e) {
      logger.severe(String.format("Failed to start the suite: %s", e.getMessage()));
      e.printStackTrace();
    }
  }
}
