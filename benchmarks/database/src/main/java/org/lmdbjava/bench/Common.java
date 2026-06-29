package org.lmdbjava.bench;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;

/**
 * Base utilities shared across all database implementations
 */
public class Common {

  protected final int threads;
  protected final File scratchDir;
  protected final Boolean runInMemory;

  protected Common(File scratchDir, int threads, Boolean runInMemory) {
    this.scratchDir = scratchDir;
    this.threads = threads;
    this.runInMemory = runInMemory;
  }

  /**
   * Create a new thread pool
   */
  protected ExecutorService createThreadPool() {
    return Executors.newFixedThreadPool(threads);
  }

  /**
   * Shutdown executor service
   */
  protected static void shutdown(ExecutorService executor) {
    executor.shutdown();
    try {
      if (!executor.awaitTermination(60, TimeUnit.SECONDS)) {
        executor.shutdownNow();
        if (!executor.awaitTermination(60, TimeUnit.SECONDS)) {
          System.err.println("Thread pool did not terminate");
        }
      }
    } catch (InterruptedException ie) {
      executor.shutdownNow();
      Thread.currentThread().interrupt();
    }
  }

  /**
   * Report database size
   */
  protected static void reportDatabaseSize(File dbFile, String dbInfo, String phase) {
    if (dbFile != null && dbFile.exists()) {
      try {
        long bytes = Files.size(dbFile.toPath());
        System.out.println("[" + dbInfo + "] file size " + phase + ": "
                + human(bytes) + " (" + bytes + " B)");
      } catch (IOException ex) {
        System.err.println("[" + dbInfo + "] cannot read file size: " + ex);
      }
    }
  }

  /**
   * Format bytes to human readable format
   */
  protected static String human(long bytes) {
    if (bytes < 1024) return bytes + " B";
    int exp = (int) (Math.log(bytes) / Math.log(1024));
    String pre = "KMG".charAt(exp - 1) + "iB";
    return String.format("%.1f %s", bytes / Math.pow(1024, exp), pre);
  }
}