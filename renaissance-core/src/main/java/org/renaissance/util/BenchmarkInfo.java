package org.renaissance.util;

import org.renaissance.Benchmark;

import java.lang.reflect.Constructor;


public final class BenchmarkInfo {

    final String className;

    public final String name;

    public final String group;

    public final String summary;

    final String description;

    public final int repetitions;

    final String[] licenses;

    public final String distro;


    BenchmarkInfo(
      String className, String name, String group, String summary, String description,
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


    public String[] summaryWords() {
      return summary.split("\\s+");
    }


    public String printableLicenses() {
      return String.join(", ", licenses);
    }


    public Benchmark loadBenchmark() {
      try {
        final ClassLoader loader = ModuleLoader.getForGroup(group);
        final Class<?> benchClass = loader.loadClass(className);
        final Constructor<?> benchCtor = benchClass.getDeclaredConstructor();

        // Make current thread as independent of the harness as possible.
        Thread.currentThread().setContextClassLoader(loader);
        return (Benchmark) benchCtor.newInstance();

      } catch (Exception e) {
        throw new RuntimeException("failed to load benchmark " + name, e);
      }
    }

}
