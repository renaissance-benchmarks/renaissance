package org.renaissance.core;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.net.MalformedURLException;
import java.net.URL;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Properties;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeSet;
import java.util.function.Predicate;
import java.util.stream.Collectors;

import static java.util.Collections.emptyMap;
import static java.util.function.Function.identity;
import static java.util.stream.Collectors.toList;
import static java.util.stream.Collectors.toSet;


/**
 * A registry of benchmarks in the suite. Represents a collection of
 * {@link BenchmarkDescriptor} instances, each of which provides access to
 * benchmark-specific information without having to load or access the
 * benchmark class.
 */
public final class BenchmarkRegistry {

  private static final String BENCHMARK_PROPERTIES = "/benchmarks.properties";

  private final Map<String, BenchmarkDescriptor> benchmarks;

  BenchmarkRegistry(final Map<String, BenchmarkDescriptor> benchmarks) {
    this.benchmarks = benchmarks;
  }


  boolean hasBenchmark(String benchmarkName) {
    return benchmarks.containsKey(benchmarkName);
  }


  BenchmarkDescriptor getBenchmark(final String benchmarkName) {
    final BenchmarkDescriptor result = benchmarks.get(benchmarkName);
    if (result != null) {
      return result;
    } else {
      throw new NoSuchElementException(String.format(
        "there is no such benchmark: %s", benchmarkName
      ));
    }
  }

  boolean hasGroup(final String groupName) {
    return groupNames().contains(groupName);
  }

  private Set<String> groupNames() {
    return benchmarks.values().stream()
      .flatMap(b -> b.groups().stream())
      .collect(toSet());
  }

  List<BenchmarkDescriptor> getGroupBenchmarks(final String groupName) {
    List<BenchmarkDescriptor> result = getMatchingBenchmarks(b -> b.groups().contains(groupName));
    if (!result.isEmpty()) {
      return result;
    } else {
      throw new NoSuchElementException(String.format(
        "there is no such group: %s", groupName
      ));
    }
  }

  public List<BenchmarkDescriptor> getMatchingBenchmarks(Predicate<BenchmarkDescriptor> matching) {
    return benchmarks.values().stream()
      .filter(matching)
      .collect(toList());
  }

  // Instance creation

  public static BenchmarkRegistry create() {
    return create(Collections.emptyMap());
  }


  static BenchmarkRegistry create(
    Map<String, String> parameterOverrides
  ) {
    final URL url = BenchmarkRegistry.class.getResource(BENCHMARK_PROPERTIES);
    return createFromProperties(url, parameterOverrides);
  }

  public static BenchmarkRegistry createFromProperties(File file) {
    try {
      final URL url = file.toURI().toURL();
      return createFromProperties(url, emptyMap());
    } catch (MalformedURLException e) {
      throw new RuntimeException("failed to create benchmark registry", e);
    }
  }


  private static BenchmarkRegistry createFromProperties(
    URL url, Map<String, String> parameterOverrides
  ) {
    try {
      // Load properties and convert it to a properly typed Map.
      Map<String, String> benchmarkProperties = toMap(loadProperties(url));

      // Extract benchmark names and create a metadata proxy for each of them.
      Map<String, BenchmarkDescriptor> benchmarks = benchmarkNames(benchmarkProperties).stream()
        .map(name -> new BenchmarkDescriptor(name, benchmarkProperties, parameterOverrides))
        .collect(Collectors.toMap(BenchmarkDescriptor::name, identity()));

      return new BenchmarkRegistry(benchmarks);

    } catch (IOException e) {
      throw new RuntimeException("failed to create benchmark registry", e);
    }
  }


  private static Properties loadProperties(URL url) throws IOException {
    try (
      // Auto-close the stream after finishing.
      final InputStream stream = url.openStream()
    ) {
      final Properties properties = new Properties();
      properties.load(stream);
      return properties;
    }
  }


  private static Map<String, String> toMap(Properties properties) {
    return properties.stringPropertyNames().stream()
      .collect(Collectors.toMap(identity(), properties::getProperty));
  }


  private static SortedSet<String> benchmarkNames(Map<String, String> properties) {
    return properties.entrySet().stream()
      .filter(e -> e.getKey().endsWith(".name"))
      .map(e -> e.getValue().trim())
      .collect(Collectors.toCollection(TreeSet::new));
  }

}
