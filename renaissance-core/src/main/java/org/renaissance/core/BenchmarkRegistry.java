package org.renaissance.core;

import org.renaissance.Benchmark;

import java.io.*;
import java.lang.reflect.Constructor;
import java.util.*;
import java.util.function.BiFunction;
import java.util.function.Function;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static java.util.stream.Collectors.*;

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
      .collect(toMap(
        properties::getProperty,
        p -> createBenchmarkInfo(properties, properties.getProperty(p)),
        (x, y) -> y,
        TreeMap::new
      ));

    // Keep groups ordered by name (order within groups implied).
    this.benchmarksByGroup = benchmarksByName.values().stream()
      .collect(groupingBy(
        b -> b.group,
        TreeMap::new,
        toList()
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


  private static BenchmarkRegistry createFromProperties(InputStream stream) {
    try {
      final Properties properties = new Properties();
      properties.load(stream);
      return new BenchmarkRegistry(properties);

    } catch (IOException e) {
      throw new RuntimeException("failed to create benchmark registry", e);
    }
  }


  private BenchmarkInfo createBenchmarkInfo(final Properties properties, String name) {
    BiFunction<String, String, String> getter = (key, defaultValue) ->
      properties.getProperty("benchmark." + name + "." + key, defaultValue);

    Function<String, String> mapper = value -> {
      if (value.startsWith("$")) {
        String tag = value.substring(1);
        if ("cpu.count".equals(tag)) {
          return Integer.toString(Runtime.getRuntime().availableProcessors());
        } else {
          throw new NoSuchElementException("unknown computed-value tag: "+ value);
        }
      }

      return value;
    };

    return new BenchmarkInfo(
      getter.apply("class", ""),
      getter.apply("name", ""),
      getter.apply("group", ""),
      getter.apply("summary", ""),
      getter.apply("description", ""),
      Integer.valueOf(getter.apply("repetitions", "20")),
      getter.apply("licenses", "").split(","),
      getter.apply("distro", ""),
      getConfigurations(name, mapper, properties)
    );
  }


  private Map<String, Map<String, String>> getConfigurations(
    String name, Function<String, String> valueMapper, Properties properties
  ) {
    Pattern pattern = Pattern.compile(
      // Match "benchmark.<name>.parameter.<configuration>.<parameter>.value
      "^benchmark[.]" + name + "[.]configuration[.](?<conf>[^.]+)[.](?<param>[^.]+)"
    );

    return properties.stringPropertyNames().stream()
      // Find matching parameter properties
      .map(pattern::matcher).filter(Matcher::matches)
      // Collect parameters in a map grouped by configuration name
      .collect(groupingBy(
        m -> m.group("conf"), toMap(
          m -> m.group("param"),
          // Map special parameter values to computed values
          m -> valueMapper.apply(properties.getProperty(m.group()))
        )
      ));
  }


  public BenchmarkInfo get(final String name) {
    return benchmarksByName.get(name);
  }

  public List<BenchmarkInfo> getAll() {
    return new ArrayList<>(benchmarksByName.values());
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


  public static Benchmark loadBenchmark(BenchmarkInfo benchInfo) {
    try {
      final ClassLoader loader = ModuleLoader.getForGroup(benchInfo.group);
      final Class<?> loadedClass = loader.loadClass(benchInfo.className);
      final Class<? extends Benchmark> benchClass = loadedClass.asSubclass(Benchmark.class);
      final Constructor<? extends Benchmark> benchCtor = benchClass.getDeclaredConstructor();

      // Make the current thread as independent of the harness as possible.
      Thread.currentThread().setContextClassLoader(loader);
      return benchCtor.newInstance();

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
          for (String conf : info.configurationNames()) {
            System.out.println("\t\t" + conf);
            for (String param : info.parameterNames(conf)) {
              System.out.printf("\t\t\t%s: %s\n", param, info.parameter(conf, param));
            }
          }
        }
      }

    } catch (Exception e) {
      System.err.println("unable to find " + detailsFile);
      System.exit(1);
    }
  }

}
