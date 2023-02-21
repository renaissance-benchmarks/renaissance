package org.renaissance.twitter.finagle

import java.util.logging.Level
import java.util.logging.Logger

object FinagleUtil {

  /**
   * Configures log levels of Finagle components to mask info messages. Unfortunately,
   * Finagle itself currently uses `java.util.logging` through its own `util-logging`
   * facade, while the included Netty libraries use `org.slf4j`. Because JUL is used
   * directly (cannot be easily replaced) and only reads the default configuration
   * from `${java.home}/lib/logging.properties` (which cannot be easily modified), we
   * set the logging level for a some of the loggers here.
   */
  def setUpLoggers(): Unit = {
    //
    // Using a custom properties files and triggering JUL reconfiguration through the
    // LogManager's `readConfiguration()` method also calls the `reset()` method, which
    // affects everybody using JUL (including the Renaissance harness). Instead, we
    // configure the log level for a few specific loggers.
    //
    // TODO Revisit logging after updating Finagle libraries.
    //
    val loggerLevels = Seq(
      // Parent for `com.twitter.jvm` and `com.twitter.app`.
      "com.twitter" -> Level.WARNING,
      // Parent for many loggers below `com.twitter.finagle`.
      "com.twitter.finagle" -> Level.WARNING,
      // `com.github.benmanes.caffeine.cache` apparently uses the root logger as parent.
      "" -> Level.WARNING
    )

    loggerLevels.foreach {
      case (name: String, level: Level) => Logger.getLogger(name).setLevel(level)
    }
  }
}
