package org.renaissance.util;

import org.renaissance.Benchmark;

import java.lang.reflect.Constructor;


public final class BenchmarkInfo {

    final String className;

    final String name;

    final String group;

    final String summary;

    final String description;

    final int repetitions;

    final String[] licenses;

    final String distro;


    BenchmarkInfo(
      String className, String name, String group,
      String summary, String description,
      int repetitions, String[] licenses, String distro
    ) {
      this.className = className;
      this.name = name;
      this.group = group;
      this.summary = summary;
      this.description = description;
      this.repetitions = repetitions;
      this.licenses = licenses;
      this.distro = distro;
    }


    public String name() { return name; }

    public String group() { return group; }

    public String summary() { return summary; }

    public String distro() { return distro; }

    public Benchmark loadBenchmark() {
      try {
        final ClassLoader loader = ModuleLoader.getForGroup(group);
        final Class<?> benchClass = loader.loadClass(className);
        final Constructor<?> benchCtor = benchClass.getDeclaredConstructor();
    public int repetitions() { return repetitions; }

        // Make current thread as independent of the harness as possible.
        Thread.currentThread().setContextClassLoader(loader);
        return (Benchmark) benchCtor.newInstance();

      } catch (Exception e) {
        throw new RuntimeException("failed to load benchmark " + name, e);
      }
    public String[] summaryWords() {
      return summary.split("\\s+");
    }


    public String printableLicenses() {
      return String.join(", ", licenses);
    }
}
