package org.renaissance.core;

import org.renaissance.BenchmarkParameter;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Optional;
import java.util.Properties;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static java.util.Arrays.stream;
import static java.util.Objects.requireNonNull;
import static java.util.function.Function.identity;
import static java.util.stream.IntStream.range;

/**
 * Provides access to benchmark metadata. The class is intended to provide
 * access to benchmark metadata without having to load the benchmark class
 * to inspect the annotations. Consequently, it is expected to be initialized
 * with metadata extracted from benchmark annotations at build time.
 */
public final class BenchmarkDescriptor {

  /** Benchmark name. */
  private final String benchmarkName;

  /** Benchmark-specific settings. */
  private final Map<String, String> benchmarkSettings;

  /** Configuration-agnostic parameter value overrides. */
  private final Map<String, String> parameterOverrides;


  BenchmarkDescriptor(
    String name, Map<String, String> settings, Map<String, String> overrides
  ) {
    benchmarkName = name;
    benchmarkSettings = settings;
    parameterOverrides = overrides;
  }

  private String settingKey(String name) {
    return String.format("benchmark.%s.%s", benchmarkName, name);
  }

  private Optional<String> settingValue(String name) {
    return Optional.ofNullable(benchmarkSettings.get(settingKey(name)));
  }

  private String requireSettingValue(String name) {
    return settingValue(name).orElseThrow(() -> new NoSuchElementException(
      String.format("benchmark '%s' has no such setting: %s", benchmarkName, name)
    ));
  }


  private List<String> toList(String value) {
    return stream(value.split(",")).map(String::trim).collect(Collectors.toList());
  }


  /** The name of the class implementing the benchmark. */
  public String className() {
    return requireSettingValue("class");
  }

  /** The name of the module the benchmark belongs to. */
  public String module() {
    return requireSettingValue("module");
  }

  /** The name of the benchmark */
  public String name() {
    return benchmarkName;
  }

  /** One-line summary of the benchmark description. */
  public String summary() {
    return requireSettingValue("summary");
  }

  /** Long description of the benchmark. */
  public String description() {
    return settingValue("description").orElse("");
  }

  /** The primary (first) workload group the benchmark belongs to. */
  public String primaryGroup() {
    return groups().get(0);
  }

  /** All the workload groups the benchmark belongs to. */
  public List<String> groups() {
    return toList(requireSettingValue("groups"));
  }

  /** Licences under which the benchmark can be distributed. */
  public List<String> licenses() {
    return toList(requireSettingValue("licenses"));
  }

  /** Benchmark distribution bundle. Depends on license. */
  public String distro() {
    return requireSettingValue("distro");
  }

  /**
   * The minimal number of repetitions the benchmark has to be executed to get
   * past the initial bulk of JIT compilations. This does NOT mean that the
   * benchmark is past its warm-up phase and exhibits stable peak performance.
   */
  public int repetitions() {
    final int defaultRepetitions = 20;
    return settingValue("repetitions").map(Integer::parseInt).orElse(defaultRepetitions);
  }

  /** Minimum JVM version required. Can be unspecified. */
  public Optional<Version> jvmVersionMin() {
    return settingValue("jvm_version_min").flatMap(this::parseVersion);
  }

  /** Maximum JVM version supported. Can be unspecified. */
  public Optional<Version> jvmVersionMax() {
    return settingValue("jvm_version_max").flatMap(this::parseVersion);
  }

  public Version scalaVersion() {
    return Version.parse(settingValue("scala_version").orElse("2.13"));
  }

  private Optional<Version> parseVersion(String stringVersion) {
    return Optional.ofNullable(
      !stringVersion.isEmpty() ? Version.parse(stringVersion) : null
    );
  }


  Configuration getConfiguration(String name) {
    if (hasConfiguration(name)) {
      return new Configuration(name);

    } else {
      throw new NoSuchElementException(String.format(
        "benchmark '%s' has no such configuration: %s", benchmarkName, name
      ));
    }
  }

  private boolean hasConfiguration(String name) {
    String prefix = String.format(
      "benchmark.%s.configuration.%s.", benchmarkName, name
    );

    return benchmarkSettings.keySet().stream()
      .anyMatch(k -> k.startsWith(prefix));
  }

  Properties toProperties() {
    Properties result = new Properties();

    String prefix = String.format("benchmark.%s.", benchmarkName);
    benchmarkSettings.entrySet().stream()
      // Only keep entries for this benchmark
      .filter(e -> e.getKey().startsWith(prefix))
      .forEach(e -> result.setProperty(e.getKey(), e.getValue()));

    return result;
  }

  final class Configuration {
    private final String configurationName;
    private final String visibleConfigurationName;

    private Configuration(String name) {
      configurationName = name;
      visibleConfigurationName = visibleName(name);
    }

    String name() {
      return visibleConfigurationName;
    }

    String benchmarkName() {
      return BenchmarkDescriptor.this.name();
    }

    String benchmarkPrimaryGroup() {
      return BenchmarkDescriptor.this.primaryGroup();
    }

    private String visibleName(String name) {
      // Modify configuration name if there is any overridden key.
      return hasOverrides() ? "modified-"+ name : name;
    }

    boolean hasOverrides() {
      return overriddenParameters().findAny().isPresent();
    }

    Stream<Parameter> overriddenParameters() {
      return parameterOverrides.keySet().stream()
        .filter(this::hasParameter).map(Parameter::new);
    }

    private boolean hasParameter(String name) {
      return benchmarkSettings.containsKey(parameterKey(name));
    }

    private String parameterKey(String name) {
      return String.format(
        "benchmark.%s.configuration.%s.%s",
        benchmarkName, configurationName, name
      );
    }

    Parameter getParameter(String name) {
      // A configuration must contain the given parameter.
      if (hasParameter(name)) {
        return new Parameter(name);

      } else {
        throw new NoSuchElementException(String.format(
          "configuration '%s' has no such parameter: %s", configurationName, name
        ));
      }
    }


    final class Parameter implements BenchmarkParameter {
      private final String parameterName;

      private Parameter(final String name) {
        parameterName = name;
      }

      String name() {
        return parameterName;
      }

      String baseValue() {
        return requireNonNull(benchmarkSettings.get(parameterKey(parameterName)));
      }

      Optional<String> overrideValue() {
        return Optional.ofNullable(parameterOverrides.get(parameterName));
      }

      private String effectiveValue() {
        return overrideValue().orElse(baseValue());
      }

      private String interpretedValue() {
        final String value = effectiveValue();
        if (value.startsWith("$")) {
          String tag = value.substring(1);
          if ("cpu.count".equals(tag)) {
            return Integer.toString(Runtime.getRuntime().availableProcessors());
          } else {
            throw new IllegalArgumentException(String.format(
              "parameter '%s' uses as unknown computed-value tag: %s",
              parameterName, value
            ));
          }
        }

        return value;
      }

      private <R> R convertedValue(String kind, Function<String, R> conversion) {
        final String value = interpretedValue();

        try {
          return conversion.apply(value);

        } catch (Throwable t) {
          throw new IllegalArgumentException(String.format(
            "benchmark '%s' expects parameter '%s' to be %s: %s",
            BenchmarkDescriptor.this.name(), parameterName, kind, value
          ));
        }
      }

      @Override
      public String value() {
        return interpretedValue();
      }

      @Override
      public boolean toBoolean() {
        return convertedValue("boolean", Boolean::parseBoolean);
      }

      @Override
      public int toInteger() {
        return convertedValue("integer", Integer::parseInt);
      }

      @Override
      public int toPositiveInteger() {
        return convertedValue("positive", Integer::parseUnsignedInt);
      }

      @Override
      public double toDouble() {
        return convertedValue("double", Double::parseDouble);
      }

      @Override
      public List<String> toList() {
        return toList(identity());
      }

      @Override
      public <T> List<T> toList(Function<String, T> parse) {
        String[] parts = trim(interpretedValue().split(","));
        return stream(parts).map(parse).collect(Collectors.toList());
      }

      private String[] trim(String[] parts) {
        return stream(parts).map(String::trim).toArray(String[]::new);
      }

      @Override
      public List<Map<String, String>> toCsvRows() {
        return toCsvRows(identity());
      }

      @Override
      public <R> List<R> toCsvRows(Function<Map<String, String>, R> parser) {
        String[] rows = trim(interpretedValue().split(";"));
        String[] names = trim(rows[0].split(","));
        return stream(rows, 1, rows.length).map(row -> {
          // Convert each row to a map of values.
          String[] cols = trim(row.split(","));
          Map<String, String> rowMap = range(0, names.length).collect(
            LinkedHashMap::new, (m, i) -> m.put(names[i], cols[i]), Map::putAll
          );

          // Convert to desired row type.
          return parser.apply(rowMap);
        }).collect(Collectors.toList());
      }
    }

  }

}
