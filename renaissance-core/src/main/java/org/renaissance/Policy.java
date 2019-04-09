package org.renaissance;

import org.renaissance.core.Dummy;

import java.util.HashMap;
import java.util.Map;
import java.util.Optional;
import java.util.function.BiFunction;
import java.util.stream.Collectors;

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
    return factories.entrySet().stream()
      .map(entry -> {
        String description = entry.getValue().apply(new Dummy(), new Config()).description();
        return new Pair<>(entry.getKey(), description);
      })
      .collect(Collectors.toMap(Pair::first, Pair::second));
  }

  static {
    factories = new HashMap<>();
    factories.put("fixed", (bench, config) -> new FixedIterationsPolicy(bench, config));
  }
}

