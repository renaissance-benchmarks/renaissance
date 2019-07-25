package org.renaissance;

import org.renaissance.harness.ExecutionPolicy;
import org.renaissance.harness.Plugin;
import org.renaissance.harness.Plugin.BenchmarkSetUpListener;
import org.renaissance.harness.Plugin.BenchmarkTearDownListener;
import org.renaissance.harness.Plugin.OperationSetUpListener;
import org.renaissance.harness.Plugin.OperationTearDownListener;
import org.renaissance.util.BenchmarkInfo;
import org.renaissance.util.DirUtils;

import java.nio.file.Path;
import java.util.List;
import java.util.concurrent.TimeUnit;

final class ExecutionDriver implements BenchmarkContext {

  private final BenchmarkInfo benchInfo;

  private final Benchmark benchmark;

  private final Config config;

  private int operationIndex;


  public ExecutionDriver(
    final BenchmarkInfo benchInfo, final Benchmark benchmark, final Config config
  ) {
    this.benchInfo = benchInfo;
    this.benchmark = benchmark;
    this.config = config;
  }


  public final void executeBenchmark() {
    final ExecutionPolicy policy = getExecutionPolicy(config.policy);
    final DaCapoStyleReporter reporter = new DaCapoStyleReporter();

    //

    benchmark.setUpBeforeAll(this);
    notifyAfterBenchmarkSetUp(benchInfo.name, config.benchmarkSetUpListeners);

    operationIndex = 0;

    do {
      reporter.operationStart(this);

      final long durationNanos = executeOperation(benchInfo.name, benchmark);

      reporter.operationEnd(this, durationNanos);

      policy.registerOperation(operationIndex, durationNanos);
      operationIndex++;
    } while (policy.keepExecuting());

    notifyBeforeBenchmarkTearDown(benchInfo.name, config.benchmarkTearDownListeners);
    benchmark.tearDownAfterAll(this);
  }


  private long executeOperation(
    final String benchName, final Benchmark bench
  ) {
    // Call benchmark and notify listeners before operation
    final long unixTsBefore = System.currentTimeMillis();
    bench.beforeIteration(this);
    notifyAfterOperationSetUp(benchName, operationIndex, config.operationSetUpListeners);

    // Execute measured operation
    final long startNanos = System.nanoTime();
    final BenchmarkResult result = bench.runIteration(this);
    final long durationNanos = System.nanoTime() - startNanos;

    // Call benchmark and notify listeners after operation
    notifyBeforeOperationTearDown(benchName, operationIndex, durationNanos, config.operationTearDownListeners);
    bench.afterIteration(this);
    final long unixTsAfter = System.currentTimeMillis();

    result.validate();

    for (final Plugin.ValidResultListener listener : config.validResultListeners) {
      listener.onValidResult(benchName, "nanos", durationNanos);
      listener.onValidResult(benchName, "unixts.before", unixTsBefore);
      listener.onValidResult(benchName, "unixts.after", unixTsAfter);
    }

    return durationNanos;
  }


  private ExecutionPolicy getExecutionPolicy(final String policyName) {
    if ("fixed-count".equalsIgnoreCase(policyName)) {
      return new CountedExecutionPolicy(
        config.repetitions > 0 ? config.repetitions : benchInfo.repetitions
      );

    } else if ("fixed-time".equalsIgnoreCase(policyName)) {
      return new TimedExecutionPolicy(config.runSeconds, TimeUnit.SECONDS);

    } else {
      throw new RuntimeException("unsupported execution policy: "+ policyName);
    }
  }


  private void notifyAfterBenchmarkSetUp(
    final String benchName, final List<BenchmarkSetUpListener> listeners
  ) {
    for (BenchmarkSetUpListener l : listeners) {
      l.afterBenchmarkSetUp(benchName);
    }
  }


  private void notifyAfterOperationSetUp(
    final String benchName, final int operationIndex,
    final List<OperationSetUpListener> listeners
  ) {
    for (OperationSetUpListener l : listeners) {
      l.afterOperationSetup(benchName, operationIndex);
    }
  }


  private void notifyBeforeOperationTearDown(
    final String benchName, final int operationIndex, long duration,
    final List<OperationTearDownListener> listeners
  ) {
    for (OperationTearDownListener l : listeners) {
      l.beforeOperationTearDown(benchName, operationIndex, duration);
    }
  }


  private void notifyBeforeBenchmarkTearDown(
    final String benchName, final List<BenchmarkTearDownListener> listeners
  ) {
    for (BenchmarkTearDownListener l : listeners) {
      l.beforeBenchmarkTearDown(benchName);
    }
  }

  // BenchmarkContext methods

  @Override
  public boolean functionalTest() {
    return config.functionalTest;
  }


  volatile Object blackHole;

  @Override
  public <T> T blackHole(final T value) {
    blackHole = value;
    blackHole = null;
    return value;
  }


  @Override
  public String benchmarkName() {
    return benchInfo.name;
  }

  @Override
  public String benchmarkGroup() {
    return benchInfo.group;
  }

  @Override
  public int operationIndex() {
    return operationIndex;
  }

  @Override
  public Path getTempDir(String name) {
    return DirUtils.generateTempDir(name);
  }


  @Override
  public Path generateTempDir(String name) {
    return DirUtils.generateTempDir(name);
  }


  @Override
  public void deleteTempDir(Path dir) {
    DirUtils.deleteTempDir(dir);
  }


  static class TimedExecutionPolicy implements ExecutionPolicy {

    private long elapsedMicros = 0;

    private final long elapsedLimitMicros;


    TimedExecutionPolicy(long elapsedLimit, TimeUnit timeUnit) {
      this.elapsedLimitMicros = timeUnit.toMicros(elapsedLimit);
    }


    @Override
    public boolean keepExecuting() {
      return elapsedMicros < elapsedLimitMicros;
    }


    @Override
    public void registerOperation(int index, long durationNanos) {
      elapsedMicros += TimeUnit.NANOSECONDS.toMicros(durationNanos);
    }

  }

  // ExecutionPolicy implementations

  static class CountedExecutionPolicy implements ExecutionPolicy {

    private final int limit;
    private int lastIndex;

    CountedExecutionPolicy(final int limit) {
      this.lastIndex = 0;
      this.limit = limit;
    }


    @Override
    public boolean keepExecuting() {
      return lastIndex + 1 < limit;
    }


    @Override
    public void registerOperation(int index, long duration) {
      lastIndex = index;
    }

  }

  //

  static final class DaCapoStyleReporter {

    void operationStart(BenchmarkContext context) {
      System.out.printf(
        "====== %s (%s), iteration %d started ======\n",
        context.benchmarkName(), context.benchmarkGroup(), context.operationIndex()
      );
    }


    void operationEnd(BenchmarkContext context, long durationNanos) {
      System.out.printf(
        "====== %s (%s), iteration %d completed (%d ms) ======\n",
        context.benchmarkName(), context.benchmarkGroup(), context.operationIndex(),
        TimeUnit.NANOSECONDS.toMillis(durationNanos)
      );
    }

  }

}

