package org.renaissance;

import java.io.IOException;
import java.nio.file.*;
import java.nio.file.attribute.BasicFileAttributes;
import java.util.Optional;
import java.util.function.BiFunction;
import java.util.regex.Pattern;

public abstract class RenaissanceBenchmark implements RenaissanceBenchmarkApi {
  public static final String kebabCase(String camelCaseName) {
    // This functionality is duplicated in the kebabCase function of the build file.
    Pattern pattern = Pattern.compile("([A-Za-z])([A-Z])");
    String result = camelCaseName;
    do {
      String last = result;
      result = pattern.matcher(result).replaceFirst("$1-$2");
      if (last == result) break;
    } while (true);
    return result.toLowerCase();
  }

  private volatile Object blackHoleField;

  public final String name() {
    String cn = this.getClass().getSimpleName();
    String camelCaseName =
      (cn.charAt(cn.length() - 1) == '$') ? cn.substring(0, cn.length() - 1) : cn;
    return kebabCase(camelCaseName);
  }

  public final String mainGroup() {
    String fullName = getClass().getName();
    String simpleName = getClass().getSimpleName();
    String packageName = fullName.substring(0, fullName.indexOf(simpleName) - 1);
    String groupName = packageName.substring("org.renaissance.".length());
    return groupName.replaceAll("\\.", "-");
  }

  public int defaultRepetitions() {
    return 20;
  }

  public abstract String description();

  public abstract License[] licenses();

  public Optional<String> initialRelease() {
    return Optional.empty();
  }

  public Optional<String> finalRelease() {
    return Optional.empty();
  }

  public void setUpBeforeAll(Config c) {
  }

  public void tearDownAfterAll(Config c) {
  }

  public void beforeIteration(Config c) {
  }

  public void afterIteration(Config c) {
  }

  public final Throwable runBenchmark(Config config) {
    try {
      setUpBeforeAll(config);
      if (!Policy.factories.containsKey(config.policy())) {
        System.err.println("Unknown policy " + config.policy() + ".");
        System.exit(1);
      }
      BiFunction<RenaissanceBenchmark, Config, Policy> factory =
        Policy.factories.get(config.policy());
      Policy policy = factory.apply(this, config);
      for (Plugin plugin : config.plugins()) {
        plugin.onStart(policy);
      }
      try {
        policy.execute();
      } finally {
        for (Plugin plugin : config.plugins()) {
          plugin.onTermination(policy);
        }
      }
      return null;
    } catch (Throwable t) {
      return t;
    } finally {
      try {
        tearDownAfterAll(config);
      } catch (Throwable t) {
        System.err.println("Error during tear-down: " + t.getMessage());
        t.printStackTrace();
      }
    }
  }

  protected <T> void blackHole(T value) {
    blackHoleField = value;
  }

  /**
   * This method runs the functionality of the benchmark.
   */
  protected abstract void runIteration(Config config);

  long runIterationWithBeforeAndAfter(Policy policy, Config config) {
    long unixTsBefore = System.currentTimeMillis();

    beforeIteration(config);

    for (Plugin plugin : config.plugins()) {
      plugin.beforeIteration(policy);
    }

    long start = System.nanoTime();

    runIteration(config);

    long end = System.nanoTime();
    long duration = end - start;

    for (Plugin plugin : config.plugins()) {
      plugin.afterIteration(policy, duration);
    }

    afterIteration(config);

    long unixTsAfter = System.currentTimeMillis();

    for (ResultObserver observer : config.resultObservers()) {
      observer.onNewResult(name(), "nanos", duration);
      observer.onNewResult(name(), "unixts.before", unixTsBefore);
      observer.onNewResult(name(), "unixts.after", unixTsAfter);
    }

    return duration;
  }

  public static void deleteTempDir(Path dirPath) {
    try {
      deleteRecursively(dirPath);
    } catch (Throwable t) {
      System.err.println("Error removing temp directory! " + t.getMessage());
    }
  }

  private static void deleteRecursively(final Path dirPath) throws IOException {
    Files.walkFileTree(dirPath, new SimpleFileVisitor<Path>() {
      @Override
      public FileVisitResult visitFile(Path file, BasicFileAttributes attrs) throws IOException {
        return delete(file);
      }

      @Override
      public FileVisitResult postVisitDirectory(Path dir, IOException exc) throws IOException {
        return delete(dir);
      }

      private FileVisitResult delete(Path path) throws IOException {
        Files.delete(path);
        return FileVisitResult.CONTINUE;
      }
    });
  }

  public static Path generateTempDir(String name) {
    Path p = null;
    try {
      p = Files.createTempDirectory(Paths.get("."), name);
    } catch (IOException e) {
      System.err.println("Error creating temp directory! " + e.getMessage());
    }
    return p;
  }
}

