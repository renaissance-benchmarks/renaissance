package org.renaissance.util;

import java.util.logging.Handler;
import java.util.logging.Level;
import java.util.logging.Logger;
import java.util.logging.SimpleFormatter;
import java.util.logging.StreamHandler;

public class Logging {
  private static final Handler STDERR_HANDLER;
  private static final Level LOG_LEVEL;
  
  static {
    STDERR_HANDLER = new StreamHandler(System.err, new SimpleFormatter());
    LOG_LEVEL = getLevel();
    STDERR_HANDLER.setLevel(LOG_LEVEL);
  }
  
  private Logging() {}

  public static Logger getLogger(String name) {
    Logger logger = Logger.getLogger(name);
    logger.setLevel(LOG_LEVEL);
    logger.addHandler(STDERR_HANDLER);
    
    return logger;
  }

  public static Logger getMethodLogger(Class<?> klass, String methodName) {
    return getLogger(String.format("%s.%s", klass.getName(), methodName));
  }

  private static Level getLevel() {
    String level = System.getProperty("org.renaissance.logging", "INFO");
    try {
      return Level.parse(level);
    } catch (IllegalArgumentException e) {
      return Level.INFO;
    }
  }
}
