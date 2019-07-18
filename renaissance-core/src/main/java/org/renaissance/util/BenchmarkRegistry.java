package org.renaissance.util;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.*;
import java.util.function.BiFunction;
import java.util.stream.Collectors;

public final class BenchmarkRegistry {

  private final Map<String, BenchmarkInfo> benchmarksByName;
  private final Map<String, List<BenchmarkInfo>> benchmarksByGroup;


  private BenchmarkRegistry(final Properties properties) {
    this.benchmarksByName = properties.stringPropertyNames().stream()
      .filter(p -> p.endsWith(".name"))
      .collect(Collectors.toMap(
        p -> properties.getProperty(p),
        p -> createBenchmarkInfo(properties, properties.getProperty(p)),
        (x, y) -> y,
        () -> new TreeMap<>()
      ));

    this.benchmarksByGroup = benchmarksByName.values().stream()
      .collect(Collectors.groupingBy(
        b -> b.group,
        () -> new TreeMap<>(),
        Collectors.toList()
      ));
  }


  public static BenchmarkRegistry createUsingProperties (InputStream propertiesAsStream) {
    try {
      final Properties properties = new Properties();
      properties.load(propertiesAsStream);
      return new BenchmarkRegistry (properties);

    } catch (IOException e) {
      throw new RuntimeException ("failed to create benchmark registry", e);
    }
  }


  private BenchmarkInfo createBenchmarkInfo(final Properties properties, String name) {
    BiFunction<String, String, String> getter = (key, defaultValue) -> {
      return properties.getProperty("benchmark." + name + "." + key, defaultValue);
    };

    return new BenchmarkInfo(
      getter.apply("class", ""),
      getter.apply("name", ""),
      getter.apply("group", ""),
      getter.apply("summary", ""),
      getter.apply("description", ""),
      Integer.valueOf(getter.apply("repetitions", "20")),
      getter.apply("licenses", "").split(","),
      getter.apply("distro", "")
    );
  }


  public BenchmarkInfo get(final String name) {
    return benchmarksByName.get(name);
  }

  public List<BenchmarkInfo> getGroup (final String groupName) {
    return Collections.unmodifiableList(benchmarksByGroup.get(groupName));
  }

  public boolean exists (final String name) {
    return benchmarksByName.containsKey(name);
  }

  public boolean groupExists (final String groupName) {
    return benchmarksByGroup.containsKey(groupName);
  }

  public Map<String, BenchmarkInfo> byName() {
    return Collections.unmodifiableMap(benchmarksByName);
  }

  public Map<String, List<BenchmarkInfo>> byGroup() {
    return Collections.unmodifiableMap(benchmarksByGroup);
  }

  public static void main (String... args) {
    String name = "benchmark-details.properties";
    File prefix = new File(new File ("target"), "classes");
    System.out.println(prefix.getAbsolutePath());

    try {
      InputStream details = new FileInputStream(new File (prefix, name));
      BenchmarkRegistry benchmarks = createUsingProperties(details);
      for (Map.Entry<String, List<BenchmarkInfo>> group : benchmarks.byGroup().entrySet()) {
        System.out.println(group.getKey());
        for (BenchmarkInfo info : group.getValue()) {
          System.out.println("\t"+ info.name);
        }
      }
    } catch (IOException e) {
      fail(name);
    }

  }


  private static void fail(String name) {
    System.err.println("unable to find resource " + name);
    System.exit(1);
  }

}
