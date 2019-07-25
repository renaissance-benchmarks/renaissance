package org.renaissance;

import org.renaissance.util.BenchmarkRegistry;
import org.renaissance.util.DirUtils;

import java.nio.file.Path;

public abstract class JmhRenaissanceBenchmark {
  protected BenchmarkContext context;

  Benchmark benchmark;

  protected abstract String benchmarkName();

  protected void defaultSetUpBeforeAll() {
    BenchmarkRegistry benchmarks = BenchmarkRegistry.createDefault();
    benchmark = benchmarks.get(benchmarkName()).loadBenchmark();

    context = createBenchmarkContext(benchmarkName());
    benchmark.setUpBeforeAll(context);
  }

  protected void defaultSetUp() {
    benchmark.beforeIteration(context);
  }

  protected void defaultTearDown() {
    benchmark.afterIteration(context);
  }

  protected void defaultTearDownAfterAll() {
    benchmark.tearDownAfterAll(context);
  }

  protected void defaultRun() {
    benchmark.runIteration(context);
  }

  //

  private BenchmarkContext createBenchmarkContext(String benchmarkName) {
    return new BenchmarkContext() {
      @Override
      public boolean functionalTest() {
        return false;
      }

      @Override
      public String benchmarkName() {
        return benchmarkName;
      }


      @Override
      public String benchmarkGroup() {
        return null;
      }


      @Override
      public int operationIndex() {
        return 0;
      }


      @Override
      public Path getTempDir(String name) {
        throw new UnsupportedOperationException("not implemented yet");
      }


      @Override
      public Path generateTempDir(String name) {
        return DirUtils.generateTempDir(name);
      }


      @Override
      public void deleteTempDir(Path dir) {
        DirUtils.deleteTempDir(dir);
      }


      volatile Object blackHole;

      @Override
      public <T> T blackHole(T value) {
        blackHole = value;
        blackHole = null;
        return value;
      }
    };
  }

}
