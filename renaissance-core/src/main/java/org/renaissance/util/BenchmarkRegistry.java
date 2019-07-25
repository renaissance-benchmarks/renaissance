package org.renaissance.util;

import org.renaissance.Benchmark;

import java.io.*;
import java.lang.reflect.Constructor;
import java.util.*;
import java.util.function.BiFunction;
import java.util.stream.Collectors;

/**
 * A registry of benchmark metadata. By default, this registry is initialized
 * using a {@link Properties} file so that it does not need to have access to
 * benchmark classes. The benchmarks and groups are kept sorted by name, both
 * globally and within groups.
 */
public final class BenchmarkRegistry {

  private final Map<String, BenchmarkInfo> benchmarksByName;

  private final Map<String, List<BenchmarkInfo>> benchmarksByGroup;

  private static final String BENCHMARK_PROPERTIES = "benchmark-details.properties";


  private BenchmarkRegistry(final Properties properties) {
    // Keep benchmarks ordered by name.
    this.benchmarksByName = properties.stringPropertyNames().stream()
      .filter(p -> p.endsWith(".name"))
      .collect(Collectors.toMap(
        p -> properties.getProperty(p),
        p -> createBenchmarkInfo(properties, properties.getProperty(p)),
        (x, y) -> y,
        () -> new TreeMap<>()
      ));

    // Keep groups ordered by name (order within groups implied).
    this.benchmarksByGroup = benchmarksByName.values().stream()
      .collect(Collectors.groupingBy(
        b -> b.group,
        () -> new TreeMap<>(),
        Collectors.toList()
      ));
  }


  public static BenchmarkRegistry createDefault() {
    final String name = "/" + BENCHMARK_PROPERTIES;
    final InputStream properties = BenchmarkRegistry.class.getResourceAsStream(name);
    if (properties == null) {
      throw new RuntimeException("could not find resource " + name);
    }

    return createFromProperties(properties);
  }


  public static BenchmarkRegistry createFromProperties(File file) throws FileNotFoundException {
    final InputStream stream = new FileInputStream(file);
    return createFromProperties(stream);
  }


  public static BenchmarkRegistry createFromProperties(InputStream stream) {
    try {
      final Properties properties = new Properties();
      properties.load(stream);
      return new BenchmarkRegistry(properties);

    } catch (IOException e) {
      throw new RuntimeException("failed to create benchmark registry", e);
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


  public List<BenchmarkInfo> getAll() {
    return new ArrayList(benchmarksByName.values());
  }


  public List<BenchmarkInfo> getGroup(final String groupName) {
    return Collections.unmodifiableList(benchmarksByGroup.get(groupName));
  }


  public boolean exists(final String name) {
    return benchmarksByName.containsKey(name);
  }


  public boolean groupExists(final String groupName) {
    return benchmarksByGroup.containsKey(groupName);
  }


  public Map<String, List<BenchmarkInfo>> byGroup() {
    return Collections.unmodifiableMap(benchmarksByGroup);
  }


  public List<String> names() {
    return new ArrayList(benchmarksByName.keySet());
  }


  public List<String> groupNames() {
    return new ArrayList(benchmarksByGroup.keySet());
  }


  public static Benchmark loadBenchmark(BenchmarkInfo benchInfo) {
    try {
      final ClassLoader loader = ModuleLoader.getForGroup(benchInfo.group);

      // Make the current thread as independent of the harness as possible.
      // ClassLoader savedLoader = Thread.currentThread().getContextClassLoader();
      Thread.currentThread().setContextClassLoader(loader);

      final Class<?> benchClass = loader.loadClass(benchInfo.className);
      final Constructor<?> benchCtor = benchClass.getDeclaredConstructor();
      final Benchmark result = (Benchmark) benchCtor.newInstance();

      // Thread.currentThread().setContextClassLoader(savedLoader);
      return result;

    } catch (Exception e) {
      throw new RuntimeException("failed to load benchmark " + benchInfo.name, e);
    }
  }


  public static void main(String... args) {
    String baseName = "benchmark-details.properties";
    File prefix = new File(new File("target"), "classes");
    File detailsFile = new File(prefix, baseName);

    try {
      System.out.println("loading benchmarks from "+ detailsFile);
      BenchmarkRegistry benchmarks = createFromProperties(detailsFile);

      for (Map.Entry<String, List<BenchmarkInfo>> group : benchmarks.byGroup().entrySet()) {
        System.out.println(group.getKey());
        for (BenchmarkInfo info : group.getValue()) {
          System.out.println("\t" + info.name);
        }
      }

    } catch (Exception e) {
      System.err.println("unable to find " + detailsFile);
      System.exit(1);
    }
  }

}
