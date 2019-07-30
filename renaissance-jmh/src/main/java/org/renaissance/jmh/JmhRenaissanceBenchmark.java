package org.renaissance.jmh;

import org.openjdk.jmh.annotations.*;
import org.renaissance.Benchmark;
import org.renaissance.BenchmarkContext;
import org.renaissance.BenchmarkResult;
import org.renaissance.util.BenchmarkInfo;
import org.renaissance.util.BenchmarkRegistry;
import org.renaissance.util.DirUtils;

import java.nio.file.Path;

import static java.util.concurrent.TimeUnit.MILLISECONDS;

public abstract class JmhRenaissanceBenchmark {
  private final Benchmark benchmark;
  private final BenchmarkContext context;
  private BenchmarkResult result;

  protected JmhRenaissanceBenchmark(final String name) {
    BenchmarkInfo benchInfo = BenchmarkRegistry.createDefault().get(name);
    benchmark = BenchmarkRegistry.loadBenchmark(benchInfo);
    context = createBenchmarkContext(benchInfo);
  }

  @Setup(Level.Trial)
  public final void setUpBenchmark() {
    benchmark.setUpBeforeAll(context);
  }

  @Setup(Level.Iteration)
  public final void setUpOperation() {
    benchmark.beforeIteration(context);
  }

  @org.openjdk.jmh.annotations.Benchmark
  @BenchmarkMode(Mode.AverageTime)
  @OutputTimeUnit(MILLISECONDS)
  @Measurement(timeUnit = MILLISECONDS)
  public final void measuredOperation() {
    result = benchmark.runIteration(context);
  }

  @TearDown(Level.Iteration)
  public final void tearDownOperation() {
    benchmark.afterIteration(context);

    result.validate();
    result = null;
  }

  @TearDown(Level.Trial)
  public final void defaultTearBenchmark() {
    benchmark.tearDownAfterAll(context);
  }

  //

  private BenchmarkContext createBenchmarkContext(BenchmarkInfo benchInfo) {
    return new BenchmarkContext() {
      @Override
      public boolean functionalTest() {
        return false;
      }

      @Override
      public String benchmarkName() {
        return benchInfo.name();
      }


      @Override
      public String benchmarkGroup() {
        return benchInfo.group();
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
