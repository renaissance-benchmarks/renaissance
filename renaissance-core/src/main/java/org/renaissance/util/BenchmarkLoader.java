package org.renaissance.util;

import org.renaissance.RenaissanceBenchmark;

public final class BenchmarkLoader {

  private final BenchmarkRegistry benchmarks;


  public BenchmarkLoader(final BenchmarkRegistry benchmarks) {
    this.benchmarks = benchmarks;
  }


  public RenaissanceBenchmark loadBenchmark(String name) {
    try {
      final BenchmarkInfo bench = benchmarks.get(name);
      final ClassLoader loader = ModuleLoader.getForGroup(bench.group);
      final Class<?> benchClass = loader.loadClass(bench.className);
      final Object result = benchClass.getDeclaredConstructor().newInstance();

      // Make current thread as independent of the harness as possible.
      Thread.currentThread().setContextClassLoader(loader);
      return (RenaissanceBenchmark) result;

    } catch (Exception e) {
      throw new RuntimeException("failed to load benchmark " + name, e);
    }
  }

}
