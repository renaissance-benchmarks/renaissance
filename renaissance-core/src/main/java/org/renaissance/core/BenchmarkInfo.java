package org.renaissance.core;

import org.renaissance.Benchmark;
import org.renaissance.BenchmarkParameter;

import java.lang.reflect.Constructor;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Optional;
import java.util.function.Function;
import java.util.stream.Collectors;

import static java.util.Arrays.stream;

/**
 * Stores metadata associated with a particular benchmark.
 * The class is intended to provide access to benchmark metadata without
 * having to load the benchmark class to inspect the annotations.
 * Consequently, it is expected to be initialized with metadata extracted
 * from benchmark annotations at build time.
 */
public final class BenchmarkInfo {

  final String module;

  final String className;

  final String name;

  final String[] groups;

  final String summary;

  final String description;

  final int repetitions;

  final String[] licenses;

  final String distro;

  /** Minimum JVM version required. Can be unspecified. */
  final Optional<Version> jvmVersionMin;

  /** Maximum JVM version supported. Can be unspecified. */
  final Optional<Version> jvmVersionMax;

  final Map<String, Map<String, String>> configurations;


  BenchmarkInfo(
    String module, String className,
    String name, String[] groups,
    String summary, String description,
    int repetitions, String[] licenses, String distro,
    Optional<Version> jvmVersionMin, Optional<Version> jvmVersionMax,
    Map<String, Map<String, String>> configurations
  ) {
    this.module = module;
    this.className = className;
    this.name = name;
    this.groups = groups;
    this.summary = summary;
    this.description = description;
    this.repetitions = repetitions;
    this.licenses = licenses;
    this.distro = distro;
    this.jvmVersionMin = jvmVersionMin;
    this.jvmVersionMax = jvmVersionMax;
    this.configurations = configurations;
  }

  /**
   * Loads this benchmark using the given module loader.
   */
  public Benchmark loadBenchmarkModule(ModuleLoader loader) {
    try {
      ClassLoader classLoader = loader.createClassLoaderForModule(module);
      Class<?> loadedClass = classLoader.loadClass(className);
      Class<? extends Benchmark> benchClass = loadedClass.asSubclass(Benchmark.class);
      Constructor<? extends Benchmark> benchCtor = benchClass.getDeclaredConstructor();

      // Make the current thread as independent of the harness as possible.
      Thread.currentThread().setContextClassLoader(classLoader);
      return benchCtor.newInstance();

    } catch (Exception e) {
      throw new RuntimeException("failed to load benchmark "+ name, e);
    }
  }

  /**
   * Resolves this benchmark's scratch directory against a given scratch
   * root directory. The purpose of this method is to provide a common
   * policy the placement of benchmark-specific scratch directories in the
   * scratch root directory.
   */
  public Path resolveScratchDir(Path scratchRootDir) {
    return scratchRootDir.resolve(module).resolve(name);
  }

  public String module() { return module; }

  public String name() { return name; }

  public String[] groups() { return Arrays.copyOf(groups, groups.length); }

  public String summary() { return summary; }

  public String distro() { return distro; }

  public int repetitions() { return repetitions; }

  public Optional<Version> jvmVersionMin() { return jvmVersionMin; }

  public Optional<Version> jvmVersionMax() { return jvmVersionMax; }

  public boolean isConfigurable() { return !configurations.isEmpty(); }

  public boolean hasConfiguration(String name) {
    return configurations.containsKey(name);
  }


  public String[] configurationNames() {
    return configurations.keySet().toArray(new String[0]);
  }


  public String[] parameterNames(String confName) {
    return getConfiguration(confName).keySet().toArray(new String[0]);
  }


  private Map<String, String> getConfiguration(String confName) {
    if (configurations.containsKey(confName)) {
      return configurations.get(confName);
    } else {
      throw new NoSuchElementException(String.format(
        "no such configuration in benchmark '%s': %s", name, confName
      ));
    }
  }


  public BenchmarkParameter parameter(String confName, String paramName) {
    final Map<String, String> conf = getConfiguration(confName);
    if (conf.containsKey(paramName)) {
      return asBenchmarkParameter(conf.get(paramName));
    } else {
      throw new NoSuchElementException(String.format(
        "no such parameter in configuration '%s': %s", confName, paramName
      ));
    }
  }

  private BenchmarkParameter asBenchmarkParameter(final String value) {
    return new BenchmarkParameter() {
      public boolean toBoolean() {
        return value(Boolean::parseBoolean);
      }

      public int toInteger() {
        return value(Integer::parseInt);
      }

      public int toPositiveInteger() {
        return value(s -> {
          int value = Integer.parseUnsignedInt(s);
          if (value > 0) {
            return value;
          } else {
            throw new NumberFormatException("the value must be positive");
          }
        });
      }

      public double toDouble() {
        return value(Double::parseDouble);
      }

      public List<String> toList() {
        return toList(Function.identity());
      }

      public <T> List<T> toList(Function<String, T> parser) {
        String[] parts = value.split(",");
        return stream(parts).map(s -> parser.apply(s.trim())).collect(Collectors.toList());
      }

      private <T> T value(Function<String, T> parser) {
          return parser.apply(value);
      }

      public String value() {
        return value;
      }
    };
  }


  public String[] licenses() {
    return Arrays.copyOf(licenses, licenses.length);
  }
}
