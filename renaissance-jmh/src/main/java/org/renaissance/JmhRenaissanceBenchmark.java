package org.renaissance;

import org.renaissance.util.BenchmarkLoader;
import org.renaissance.util.BenchmarkRegistry;

public abstract class JmhRenaissanceBenchmark {
  private Config config = new Config();
  RenaissanceBenchmark benchmark;

  protected abstract String benchmarkName();

  protected void defaultSetUpBeforeAll() {
    BenchmarkRegistry registry = BenchmarkRegistry.createDefault();
    BenchmarkLoader loader = new BenchmarkLoader(registry);
    benchmark = loader.loadBenchmark(benchmarkName());
    benchmark.setUpBeforeAll(config);
  }

  protected void defaultSetUp() {
    benchmark.beforeIteration(config);
  }

  protected void defaultTearDown() {
    benchmark.afterIteration(config);
  }

  protected void defaultTearDownAfterAll() {
    benchmark.tearDownAfterAll(config);
  }

  protected void defaultRun() {
    benchmark.runIteration(config);
  }
}
