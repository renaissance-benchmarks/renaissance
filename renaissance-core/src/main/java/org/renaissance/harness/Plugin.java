package org.renaissance.harness;

/**
 * Marker interface for harness plugins. Plugins are loaded dynamically and
 * each {@link Plugin} implementation must have a zero arguments constructor.
 */
public interface Plugin {

  interface HarnessInitListener {
    /**
     * Called before setting up the first benchmark (before calling its set up
     * method), after initializing the harness.
     */
    void afterHarnessInit();
  }

  interface HarnessShutdownListener {
    /**
     * Called after the last benchmark finished executing (after calling its
     * tear down method), before the harness exits.
     */
    void beforeHarnessShutdown();
  }

  interface BenchmarkSetUpListener {
    /**
     * Called before first execution of the measured operation, after calling
     * the benchmark set up method.
     *
     * @param benchmark Name of the benchmark.
     */
    void afterBenchmarkSetUp(String benchmark);
  }

  interface BenchmarkTearDownListener {
    /**
     * Called after last execution of the measured operation, before calling
     * the benchmark tear down method.
     *
     * @param benchmark Name of the benchmark.
     */
    void beforeBenchmarkTearDown(String benchmark);
  }

  interface OperationSetUpListener {
    /**
     * Called before executing the measured operation, after calling the
     * operation set up method.
     *
     * @param benchmark Name of the benchmark.
     * @param opIndex Index of the measured operation execution.
     * @param isLastOp {@code true} if this is the last execution of the
     *   measured operation, {@code false} otherwise (or if unknown).
     */
    void afterOperationSetUp(String benchmark, int opIndex, boolean isLastOp);
  }

  interface OperationTearDownListener {
    /**
     * Called after the benchmark finished executing the measured operation,
     * before calling the operation tear down method.
     *
     * @param benchmark Name of the benchmark.
     * @param opIndex Index of the measured operation execution.
     * @param durationNanos Duration of the measured operation in nanoseconds.
     */
    void beforeOperationTearDown(String benchmark, int opIndex, long durationNanos);
  }

  interface BenchmarkResultListener {
    /**
     * Called when a benchmark produces a new (valid) result. Will be called
     * after completion of the measured benchmark operation, i.e., never inside
     * the measured code.
     *
     * @param benchmark Name of the benchmark.
     * @param metric Result name (e.g. branch-misses).
     * @param value Actual value of the metric.
     */
    void onBenchmarkResult(String benchmark, String metric, long value);
  }

  interface BenchmarkFailureListener {
    /**
     * Called whenever a benchmark fails during set up, tear down, or operation
     * (including operation set up and tear down). There will be no more
     * results for the given benchmark after this event.
     *
     * @param benchmark Name of the benchmark.
     */
    void onBenchmarkFailure(String benchmark);
  }
}
