package org.renaissance.core;

import org.renaissance.Benchmark;

import java.lang.reflect.Constructor;
import java.util.Arrays;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Optional;

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
        "no such configuration in benchmark %s: %s", name, confName
      ));
    }
  }


  public String parameter(String confName, String paramName) {
    final Map<String, String> conf = getConfiguration(confName);
    if (conf.containsKey(paramName)) {
      return conf.get(paramName);
    } else {
      throw new NoSuchElementException(String.format(
        "no such parameter in benchmark %s configuration %s: %s",
        name, confName, paramName
      ));
    }
  }

  public String[] licenses() {
    return Arrays.copyOf(licenses, licenses.length);
  }
}
