package org.renaissance.jmh;

import org.openjdk.jmh.annotations.*;
import org.renaissance.Benchmark;
import org.renaissance.BenchmarkContext;
import org.renaissance.BenchmarkResult;
import org.renaissance.BenchmarkResult.ValidationException;
import org.renaissance.core.BenchmarkInfo;
import org.renaissance.core.BenchmarkRegistry;

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
    benchmark.setUpBeforeEach(context);
  }

  @org.openjdk.jmh.annotations.Benchmark
  @BenchmarkMode(Mode.AverageTime)
  @OutputTimeUnit(MILLISECONDS)
  @Measurement(timeUnit = MILLISECONDS)
  public final void runOperation() {
    result = benchmark.run(context);
  }

  @TearDown(Level.Iteration)
  public final void tearDownOperation() throws ValidationException {
    benchmark.tearDownAfterEach(context);

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
      public int intParameter(String name) {
        return Integer.parseInt(stringParameter(name));
      }


      @Override
      public double doubleParameter(String name) {
        return Double.parseDouble(stringParameter(name));
      }


      @Override
      public String stringParameter(String name) {
        return benchInfo.parameter("jmh", name);
      }

    };
  }

}
