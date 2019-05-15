package org.renaissance;

import org.renaissance.util.Logging;
import org.renaissance.util.ModuleLoader;
import org.renaissance.util.ModuleLoadingException;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.logging.Logger;

public class Launcher {
  public static void main(String args[]) {
    final Logger logger = Logging.getMethodLogger(Launcher.class, "main");

    try {
      final ClassLoader loader = ModuleLoader.getForGroup("renaissance-harness");
      final Class<?> suiteClass = loader.loadClass("org.renaissance.RenaissanceSuite");
      final Method suiteMain = suiteClass.getMethod("main", String[].class);
      suiteMain.invoke(null, new Object[] { args });

    } catch (ModuleLoadingException e) {
      logger.severe(message("Failed to load harness: ", e));
      System.exit(1);

    } catch (InvocationTargetException e) {
      logger.severe(message("Harness failed with exception: ", e.getCause()));
      System.exit(1);

    } catch (ReflectiveOperationException e) {
      logger.severe(message("Failed to initialize harness: ", e));
      System.exit(1);
    }
  }


  private static String message(final String prefix, Throwable cause) {
    final ByteArrayOutputStream bytes = new ByteArrayOutputStream();
    final PrintStream printer = new PrintStream(bytes);

    printer.append(prefix);
    cause.printStackTrace(printer);
    printer.close();

    return new String(bytes.toByteArray());
  }

}
