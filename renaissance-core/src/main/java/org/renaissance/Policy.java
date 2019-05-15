package org.renaissance;

import java.util.HashMap;
import java.util.Map;
import java.util.Optional;
import java.util.function.BiFunction;
import java.util.stream.Collectors;

import static org.renaissance.RenaissanceBenchmark.kebabCase;

/** The policy that executes the benchmark
 */
public abstract class Policy {
  public abstract String description();

  /** The benchmark that is executing.
   */
  public abstract RenaissanceBenchmark currentBenchmark();

  /** Runs the benchmark multiple times.
   */
  public abstract Optional<Throwable> execute();

  /** The name of the benchmark that is currently executing.
   */
  public String currentBenchmarkName() {
    return currentBenchmark().name();
  }

  public static Map<String, BiFunction<RenaissanceBenchmark, Config, Policy>> factories;


  public static Map<String, String> descriptions() {
    // TODO Get rid of this dummy. Policies need to be loaded differently.
    final RenaissanceBenchmark dummy = new RenaissanceBenchmark() {
      @Override
      protected void runIteration(Config config) {}
    };

    return factories.entrySet().stream()
      .map(entry -> {
        String description = entry.getValue().apply(dummy, new Config()).description();
        return new Pair<>(entry.getKey(), description);
      })
      .collect(Collectors.toMap(Pair::first, Pair::second));
  }

  public static String kebabCasePolicy(Class<?> cls) {
    String className = cls.getSimpleName();
    int prefixLength = className.length() - Policy.class.getSimpleName().length();
    String shortName = className.substring(0, prefixLength);
    return kebabCase(shortName);
  }

  static {
    factories = new HashMap<>();
    factories.put(
      kebabCasePolicy(FixedIterationsPolicy.class),
      (bench, config) -> new FixedIterationsPolicy(bench, config));
    factories.put(
      kebabCasePolicy(FixedWarmupPolicy.class),
      (bench, config) -> new FixedWarmupPolicy(bench, config));
  }
}

