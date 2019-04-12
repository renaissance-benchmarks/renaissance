package org.renaissance;

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
    String groupName = packageName.substring(packageName.lastIndexOf('.') + 1);
    return groupName;
  }

  public int defaultRepetitions() {
    return 20;
  }

  public abstract String description();

  public abstract License[] licenses();

  public License distro() {
    return License.distro(licenses());
  }

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

  public final Optional<Throwable> runBenchmark(Config config) {
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
      return Optional.empty();
    } catch (Throwable t) {
      return Optional.of(t);
    } finally {
      try {
        tearDownAfterAll(config);
      } catch (Throwable t) {
        System.err.println("Error during tear-down: " + t.getMessage());
        t.printStackTrace();
      }
    }
  }

  private volatile Object blackHoleField;

  protected <T> void blackHole(T value) {
    blackHoleField = value;
  }

  /** This method runs the functionality of the benchmark.
   */
  protected abstract void runIteration(Config config);

  long runIterationWithBeforeAndAfter(Policy policy, Config config) {
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

    return duration;
  }

}

