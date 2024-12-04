package org.renaissance.core;

import java.util.logging.ConsoleHandler;
import java.util.logging.Level;
import java.util.logging.Logger;
import java.util.logging.StreamHandler;

public final class Logging {
  private static final String FORMAT_PROPERTY = "java.util.logging.SimpleFormatter.format";
  private static final String DEFAULT_FORMAT = "[%1$tFT%1$tT.%1$tL%1$tz] %3$s (%2$s)%n%4$s: %5$s%n%6$s";

  // Keep a strong reference to the (configured) logger.
  private static final Logger rootLogger = createRootLogger();

  private static Logger createRootLogger() {
    // Create a handler for all logging levels.
    final StreamHandler handler = createHandler();
    handler.setLevel(Level.ALL);

    // Create root logger with the specified logging level.
    final Logger result = Logger.getLogger("org.renaissance");
    result.addHandler(handler);
    result.setLevel(getLogLevel());
    return result;
  }

  private static StreamHandler createHandler() {
    // Set a property to configure the output of SimpleFormatter.
    if (System.getProperty(FORMAT_PROPERTY) == null) {
      System.setProperty(FORMAT_PROPERTY, DEFAULT_FORMAT);
    }

    // Creates SimpleFormatter AFTER setting the system property.
    return new ConsoleHandler();
  }

  private Logging() {}

  public static Logger getLogger(String name) {
    return Logger.getLogger(name);
  }

  public static Logger getPackageLogger(Class<?> klass) {
    return Logger.getLogger(klass.getPackage().getName());
  }

  private static Level getLogLevel() {
    String level = System.getProperty("org.renaissance.logging", "INFO");
    try {
      return Level.parse(level);
    } catch (IllegalArgumentException e) {
      return Level.INFO;
    }
  }
}
