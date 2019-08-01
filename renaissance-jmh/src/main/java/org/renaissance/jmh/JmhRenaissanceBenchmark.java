package org.renaissance.jmh;

import org.openjdk.jmh.annotations.*;
import org.renaissance.Benchmark;
import org.renaissance.BenchmarkContext;
import org.renaissance.BenchmarkResult;
import org.renaissance.util.BenchmarkInfo;
import org.renaissance.util.BenchmarkRegistry;

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
      }


      @Override
      }


      @Override
      }

    };
  }

}
