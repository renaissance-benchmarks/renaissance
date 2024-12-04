package org.renaissance.core;

import java.io.Closeable;
import java.io.IOException;
import java.nio.file.Path;
import java.util.LinkedHashSet;
import java.util.Objects;
import java.util.Set;

final class Cleaner {
  private static Set<Closeable> registeredCloseables = new LinkedHashSet<>();
  private static Set<Path> registeredPaths = new LinkedHashSet<>();

  private Cleaner() {}

  static Path deleteOnExit(Path path) {
    return register(registeredPaths, path);
  }

  static <T extends Closeable> T closeOnExit(T closeable) {
    return register(registeredCloseables, closeable);
  }

  private synchronized static <T> T register(Set<? super T> registry, T item) {
    if (registry == null) {
      throw new IllegalStateException("Shutdown in progress");
    } else {
      registry.add(Objects.requireNonNull(item));
    }

    return item;
  }

  private static void run() {
    Set<Closeable> closeables;
    Set<Path> paths;

    synchronized (Cleaner.class) {
      closeables = registeredCloseables;
      registeredCloseables = null;

      paths = registeredPaths;
      registeredPaths = null;
    }

    // Close closeables BEFORE deleting files/directories.
    // In particular URLClassLoader instances which keep files open.
    // Delete files/directories AFTER closing closeables.

    cleanupEach(closeables, "close", Closeable::close).clear();
    cleanupEach(paths, "delete", DirUtils::deleteRecursively).clear();
  }

  @FunctionalInterface
  private interface Action<T> {
    void accept(T object) throws IOException;
  }

  private static <T, C extends Iterable<T>> C cleanupEach(C items, String name, Action<T> action) {
    for (T item : items) {
      try {
        action.accept(item);
      } catch (IOException e) {
        // Just a notification. This should be rare and is not critical.
        System.err.format("warning: failed to %s %s on shutdown: %s\n", name, item, e);
      }
    }

    return items;
  }

  static {
    Runtime.getRuntime().addShutdownHook(new Thread(Cleaner::run));
  }

}
