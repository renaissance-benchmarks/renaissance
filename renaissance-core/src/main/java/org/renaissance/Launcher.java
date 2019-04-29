package org.renaissance;

import java.lang.reflect.Method;
import java.util.logging.Logger;

import org.renaissance.util.Logging;
import org.renaissance.util.ModuleLoader;
import org.renaissance.util.ModuleLoadingException;

public class Launcher {
  public static void main(String args[]) {
    Logger logger = Logging.getMethodLogger(Launcher.class, "main");

    try {
      ClassLoader loader = ModuleLoader.getForGroup("renaissance-harness");
      Class<?> suiteClass = loader.loadClass("org.renaissance.RenaissanceSuite");
      Method suiteMain = suiteClass.getMethod("main", String[].class);
      suiteMain.invoke(null, new Object[] { args });
    } catch (ReflectiveOperationException|ModuleLoadingException e) {
      logger.severe(String.format("Failed to start the suite: %s", e.getMessage()));
      e.printStackTrace();
      System.exit(1);
    }
  }
}
