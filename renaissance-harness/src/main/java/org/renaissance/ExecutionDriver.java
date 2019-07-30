package org.renaissance;

import org.renaissance.harness.ExecutionPolicy;
import org.renaissance.harness.Plugin.*;
import org.renaissance.util.BenchmarkInfo;
import org.renaissance.util.DirUtils;

import java.nio.file.Path;
import java.util.concurrent.TimeUnit;

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

    //

    benchmark.setUpBeforeAll(this);
    dispatcher.notifyAfterBenchmarkSetUp(benchInfo.name());

    operationIndex = 0;

    do {
      printStartInfo(operationIndex, benchInfo.name(), benchInfo.group());

      final long durationNanos = executeOperation(
        operationIndex, benchInfo.name(), benchmark, dispatcher,
        policy.isLastOperation()
      );

      printEndInfo(operationIndex, benchInfo.name(), benchInfo.group(), durationNanos);
      policy.registerOperation(operationIndex, durationNanos);

      operationIndex++;
    } while (policy.keepExecuting());

    dispatcher.notifyBeforeBenchmarkTearDown(benchInfo.name());
    benchmark.tearDownAfterAll(this);
  }


  private long executeOperation(
    final int opIndex, final String benchName, final Benchmark bench,
    final EventDispatcher dispatcher, final boolean isLast
  ) {
    // Call benchmark and notify listeners before operation
    final long unixTsBefore = System.currentTimeMillis();
    bench.beforeIteration(this);
    dispatcher.notifyAfterOperationSetUp(benchName, opIndex, isLast);

    // Execute measured operation
    final long startNanos = System.nanoTime();
    final BenchmarkResult result = bench.runIteration(this);
    final long durationNanos = System.nanoTime() - startNanos;

    // Call benchmark and notify listeners after operation
    dispatcher.notifyBeforeOperationTearDown(benchName, opIndex, durationNanos);
    bench.afterIteration(this);
    final long unixTsAfter = System.currentTimeMillis();

    result.validate();

    // Provide basic results to listeners
    dispatcher.notifyOnValidResult(benchName, "nanos", durationNanos);
    dispatcher.notifyOnValidResult(benchName, "unixts.before", unixTsBefore);
    dispatcher.notifyOnValidResult(benchName, "unixts.after", unixTsAfter);

    return durationNanos;
  }


  private ExecutionPolicy getExecutionPolicy(Config config) {
    String policyName = config.policy;
    if ("fixed-count".equalsIgnoreCase(policyName)) {
      return new CountedExecutionPolicy(
        config.repetitions > 0 ? config.repetitions : benchInfo.repetitions()
      );

    } else if ("fixed-time".equalsIgnoreCase(policyName)) {
      return new TimedExecutionPolicy(config.runSeconds, TimeUnit.SECONDS);

    } else {
      throw new RuntimeException("unsupported execution policy: "+ policyName);
    }
  }


  void printStartInfo(int index, String name, String group) {
    System.out.printf(
      "====== %s (%s), iteration %d started ======\n",
      name, group, index
    );
  }


  void printEndInfo(int index, String name, String group, long durationNanos) {
    final double durationMillis = durationNanos / 1e6;

    System.out.printf(
      "====== %s (%s), iteration %d completed (%.3f ms) ======\n",
      name, group, index, durationMillis
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
    private final ValidResultListener[] validResultListeners;

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

      validResultListeners = config.validResultListeners.toArray(
        new ValidResultListener[0]
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
      final String benchName, final int operationIndex, final boolean isLast
    ) {
      for (final OperationSetUpListener l : operationSetUpListeners) {
        l.afterOperationSetUp(benchName, operationIndex, isLast);
      }
    }


    void notifyBeforeOperationTearDown(
      final String benchName, final int operationIndex, long duration
    ) {
      for (final OperationTearDownListener l : operationTearDownListeners) {
        l.beforeOperationTearDown(benchName, operationIndex, duration);
      }
    }


    void notifyOnValidResult(
      final String benchName, final String metric, final long value
    ) {
      for (final ValidResultListener l : validResultListeners) {
        l.onValidResult(benchName, metric, value);
      }
    }
  }
}

