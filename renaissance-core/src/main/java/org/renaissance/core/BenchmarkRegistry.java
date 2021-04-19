package org.renaissance.core;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Optional;
import java.util.Properties;
import java.util.TreeMap;
import java.util.function.BiFunction;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static java.util.Collections.unmodifiableList;
import static java.util.Collections.unmodifiableMap;
import static java.util.stream.Collectors.groupingBy;
import static java.util.stream.Collectors.toList;
import static java.util.stream.Collectors.toMap;

/**
 * A registry of benchmark metadata. By default, this registry is initialized
 * using a {@link Properties} file so that it does not need to have access to
 * benchmark classes. The benchmarks and primary groups are kept sorted.
 */
public final class BenchmarkRegistry {

  private static final String BENCHMARK_PROPERTIES = "benchmarks.properties";

  private final Map<String, BenchmarkInfo> benchmarksByName;

  private final Map<String, List<BenchmarkInfo>> benchmarksByPrimaryGroup;


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

    // Keep primary groups ordered by name (order within groups implied).
    this.benchmarksByPrimaryGroup = benchmarksByName.values().stream()
      .collect(groupingBy(
        b -> b.groups()[0],
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
      properties.getProperty("benchmark." + name + "." + key, defaultValue).trim();

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
      getter.apply("module", ""),
      getter.apply("class", ""),
      getter.apply("name", ""),
      getter.apply("groups", "").split(","),
      getter.apply("summary", ""),
      getter.apply("description", ""),
      Integer.parseInt(getter.apply("repetitions", "20")),
      getter.apply("licenses", "").split(","),
      getter.apply("distro", ""),
      parseJvmVersion(getter.apply("jvm_version_min", "")),
      parseJvmVersion(getter.apply("jvm_version_max", "")),
      getConfigurations(name, mapper, properties)
    );
  }


  private Optional<Version> parseJvmVersion(String stringVersion) {
    return Optional.ofNullable(
      !stringVersion.isEmpty() ? Version.parse(stringVersion) : null
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


  public List<BenchmarkInfo> getMatching(Predicate<BenchmarkInfo> matcher) {
    return benchmarksByName.values().stream().filter(matcher).collect(toList());
  }


  public List<BenchmarkInfo> getGroup(final String groupName) {
    return unmodifiableList(benchmarksByPrimaryGroup.get(groupName));
  }


  public boolean exists(final String name) {
    return benchmarksByName.containsKey(name);
  }


  public boolean groupExists(final String groupName) {
    return benchmarksByPrimaryGroup.containsKey(groupName);
  }


  public Map<String, List<BenchmarkInfo>> byGroup() {
    return unmodifiableMap(benchmarksByPrimaryGroup);
  }


  static void main(String... args) {
    File prefix = new File(new File("target"), "classes");
    File detailsFile = new File(prefix, BENCHMARK_PROPERTIES);

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
