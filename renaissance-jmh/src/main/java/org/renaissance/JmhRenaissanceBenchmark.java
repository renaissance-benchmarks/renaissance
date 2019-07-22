package org.renaissance;

import org.renaissance.util.BenchmarkRegistry;

public abstract class JmhRenaissanceBenchmark {
  private Config config = new Config();
  RenaissanceBenchmark benchmark;

  protected abstract String benchmarkName();

  protected void defaultSetUpBeforeAll() {
    BenchmarkRegistry benchmarks = BenchmarkRegistry.createDefault();
    benchmark = benchmarks.get(benchmarkName()).loadBenchmark();
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
