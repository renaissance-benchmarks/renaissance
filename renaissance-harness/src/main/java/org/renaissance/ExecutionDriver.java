package org.renaissance;

import org.renaissance.Config.ExecutionPolicyType;
import org.renaissance.harness.ExecutionPolicy;
import org.renaissance.harness.Plugin.*;
import org.renaissance.util.BenchmarkInfo;
import org.renaissance.util.DirUtils;

import java.nio.file.Path;
import java.util.concurrent.TimeUnit;

/**
 * Benchmark execution driver. Captures the sequence of actions performed
 * during benchmark execution (i.e., calling the sequencing methods on a
 * benchmark and issuing notifications to event listeners) and maintains
 * execution context.
 */
final class ExecutionDriver implements BenchmarkContext {

  private final BenchmarkInfo benchInfo;

  private final Config config;

  private int operationIndex;


  public ExecutionDriver(
    final BenchmarkInfo benchInfo, final Config config
  ) {
    this.benchInfo = benchInfo;
    this.config = config;
  }


  public final void executeBenchmark(Benchmark benchmark) {
    final ExecutionPolicy policy = getExecutionPolicy(config);
    final EventDispatcher dispatcher = new EventDispatcher(config);

    benchmark.setUpBeforeAll(this);

    try {
      dispatcher.notifyAfterBenchmarkSetUp(benchInfo.name());

      try {
        operationIndex = 0;

        do {
          printStartInfo(operationIndex, benchInfo);

          final long durationNanos = executeOperation(
            operationIndex, benchInfo.name(), benchmark,
            dispatcher, policy.isLastOperation()
          );

          printEndInfo(operationIndex, benchInfo, durationNanos);
          policy.registerOperation(operationIndex, durationNanos);

          operationIndex++;
        } while (policy.keepExecuting());

      } finally {
        dispatcher.notifyBeforeBenchmarkTearDown(benchInfo.name());
      }

    } finally {
      benchmark.tearDownAfterAll(this);
    }
  }


  private long executeOperation(
    final int opIndex, final String benchName, final Benchmark bench,
    final EventDispatcher dispatcher, final boolean isLast
  ) {
    //
    // Call the benchmark and notify listeners before the measured operation.
    // Nothing should go between the measured operation call and the timing
    // calls. If everything goes well, we notify the listeners and call the
    // benchmark after the measured operation and try to validate the result.
    // If the result is valid, we notify listeners about basic result metrics
    // and return the duration of the measured operation, otherwise an
    // exception is thrown and the method terminates prematurely.
    //
    final long unixTsBefore = System.currentTimeMillis();
    bench.beforeIteration(this);
    dispatcher.notifyAfterOperationSetUp(benchName, opIndex, isLast);

    final long startNanos = System.nanoTime();
    final BenchmarkResult result = bench.runIteration(this);
    final long durationNanos = System.nanoTime() - startNanos;

    dispatcher.notifyBeforeOperationTearDown(benchName, opIndex, durationNanos);
    bench.afterIteration(this);
    final long unixTsAfter = System.currentTimeMillis();

    result.validate();

    dispatcher.notifyOnBenchmarkResult(benchName, "nanos", durationNanos);
    dispatcher.notifyOnBenchmarkResult(benchName, "unixts.before", unixTsBefore);
    dispatcher.notifyOnBenchmarkResult(benchName, "unixts.after", unixTsAfter);

    return durationNanos;
  }


  private ExecutionPolicy getExecutionPolicy(Config config) {
    final ExecutionPolicyType policyType = config.policyType;
    if (policyType == ExecutionPolicyType.FIXED_COUNT) {
      return new CountedExecutionPolicy(
        config.repetitions > 0 ? config.repetitions : benchInfo.repetitions()
      );

    } else if (policyType == ExecutionPolicyType.FIXED_TIME) {
      return new TimedExecutionPolicy(config.runSeconds, TimeUnit.SECONDS);

    } else {
      throw new RuntimeException("unsupported execution policy: "+ policyType);
    }
  }


  void printStartInfo(int index, BenchmarkInfo benchInfo) {
    System.out.printf(
      "====== %s (%s), iteration %d started ======\n",
      benchInfo.name(), benchInfo.group(), index
    );
  }


  void printEndInfo(int index, BenchmarkInfo benchInfo, long durationNanos) {
    final double durationMillis = durationNanos / 1e6;

    System.out.printf(
      "====== %s (%s), iteration %d completed (%.3f ms) ======\n",
      benchInfo.name(), benchInfo.group(), index, durationMillis
    );
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
    return benchInfo.name();
  }

  @Override
  public String benchmarkGroup() {
    return benchInfo.group();
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

  // ExecutionPolicy implementations

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


    @Override
    public boolean isLastOperation() { return false; }

  }


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


    @Override
    public boolean isLastOperation() { return lastIndex + 1 >= limit; }

  }

  //

  private static final class EventDispatcher {
    private final BenchmarkSetUpListener[] benchmarkSetUpListeners;
    private final BenchmarkTearDownListener[] benchmarkTearDownListeners;
    private final OperationSetUpListener[] operationSetUpListeners;
    private final OperationTearDownListener[] operationTearDownListeners;
    private final BenchmarkResultListener[] benchmarkResultListeners;

    EventDispatcher(Config config) {
      benchmarkSetUpListeners = config.benchmarkSetUpListeners.toArray(
        new BenchmarkSetUpListener[0]
      );

      benchmarkTearDownListeners = config.benchmarkTearDownListeners.toArray(
        new BenchmarkTearDownListener[0]
      );

      operationSetUpListeners = config.operationSetUpListeners.toArray(
        new OperationSetUpListener[0]
      );

      operationTearDownListeners = config.operationTearDownListeners.toArray(
        new OperationTearDownListener[0]
      );

      benchmarkResultListeners = config.benchmarkResultListeners.toArray(
        new BenchmarkResultListener[0]
      );
    }

    void notifyAfterBenchmarkSetUp(final String benchName) {
      for (final BenchmarkSetUpListener l : benchmarkSetUpListeners) {
        l.afterBenchmarkSetUp(benchName);
      }
    }


    void notifyBeforeBenchmarkTearDown(final String benchName) {
      for (final BenchmarkTearDownListener l : benchmarkTearDownListeners) {
        l.beforeBenchmarkTearDown(benchName);
      }
    }


    void notifyAfterOperationSetUp(
      final String benchName, final int opIndex, final boolean isLastOp
    ) {
      for (final OperationSetUpListener l : operationSetUpListeners) {
        l.afterOperationSetUp(benchName, opIndex, isLastOp);
      }
    }


    void notifyBeforeOperationTearDown(
      final String benchName, final int opIndex, long durationNanos
    ) {
      for (final OperationTearDownListener l : operationTearDownListeners) {
        l.beforeOperationTearDown(benchName, opIndex, durationNanos);
      }
    }


    void notifyOnBenchmarkResult(
      final String benchName, final String metric, final long value
    ) {
      for (final BenchmarkResultListener l : benchmarkResultListeners) {
        l.onBenchmarkResult(benchName, metric, value);
      }
    }
  }

}

