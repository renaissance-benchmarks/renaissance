package org.renaissance;

/**
 * Marker interface for harness plugins. Plugins are loaded dynamically and
 * each {@link Plugin} implementation must have a zero arguments constructor.
 */
public interface Plugin {

  /**
   * Indicates that a plugin wants to be notified after the harness finished
   * initializing, before it starts to set up the first of the benchmarks.
   */
  interface HarnessInitListener extends Plugin {
    /**
     * Called before setting up the first benchmark (before calling its set up
     * method), after initializing the harness.
     */
    void afterHarnessInit();
  }

  /**
   * Indicates that a plugin wants to be notified before the harness shuts down,
   * after it has torn down the last of the benchmarks.
   */
  interface HarnessShutdownListener extends Plugin {
    /**
     * Called after the last benchmark finished executing (after calling its
     * tear down method), before the harness exits.
     */
    void beforeHarnessShutdown();
  }

  /**
   * Indicates that a plugin wants to be notified before executing the first
   * measured operation, after the benchmark has been set up by the harness.
   */
  interface BenchmarkSetUpListener extends Plugin {
    /**
     * Called before first execution of the measured operation, after calling
     * the benchmark set up method.
     *
     * @param benchmark Name of the benchmark.
     */
    void afterBenchmarkSetUp(String benchmark);
  }

  /**
   * Indicates that a plugin wants to be notified after executing the last
   * measured operation, before the benchmark has been torn down by the harness.
   */
  interface BenchmarkTearDownListener extends Plugin {
    /**
     * Called after last execution of the measured operation, before calling
     * the benchmark tear down method.
     *
     * @param benchmark Name of the benchmark.
     */
    void beforeBenchmarkTearDown(String benchmark);
  }

  /**
   * Indicates that a plugin wants to be notified before each execution of the
   * measured operation, after it has been set up by the harness.
   */
  interface OperationSetUpListener extends Plugin {
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

  /**
   * Indicates that a plugin wants to be notified after each execution of the
   * measured operation, before it has been torn down by the harness.
   */
  interface OperationTearDownListener extends Plugin {
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

  /**
   * Indicates that a plugin wants to be notified about measurement results.
   */
  interface MeasurementResultListener extends Plugin {
    /**
     * Notifies the listener about new measurement result. May be called multiple times
     * after completion of the measured operation (i.e.m never inside the measured code),
     * but only if the {@link BenchmarkResult} returned by the measured operation is valid.
     *
     * @param benchmark Name of the benchmark.
     * @param metric The name of the result metric (e.g. branch-misses).
     * @param value The value of the result metric.
     */
    void onMeasurementResult(String benchmark, String metric, long value);
  }

  /**
   * Indicates that a plugin is a provider of measurement results.
   */
  interface MeasurementResultPublisher extends Plugin {
    /**
     * Notifies the listener (result publisher) that it is time to publish measurement
     * results (if any). Will be called once after completion of the measured operation,
     * after the {@link OperationTearDownListener#beforeOperationTearDown(String, int, long) beforeOperationTearDown}
     * event, but only if the {@link BenchmarkResult} returned by the measured operation is valid.
     * The listener should use the provided {@code dispatcher} to broadcast measurement
     * results to measurement result consumers.
     *
     * @param benchmark Name of the benchmark.
     * @param opIndex Index of the measured operation execution.
     * @param dispatcher Callback interface for publishing measurement results.
     */
    void onMeasurementResultsRequested(String benchmark, int opIndex, MeasurementResultListener dispatcher);
  }

  /**
   * Indicates that a plugin wants to be notified when a benchmark fails.
   */
  interface BenchmarkFailureListener extends Plugin {
    /**
     * Called whenever a benchmark fails during set up, tear down, or operation
     * (including operation set up and tear down). There will be no more
     * measurement results for the given benchmark after this event.
     *
     * @param benchmark Name of the benchmark.
     */
    void onBenchmarkFailure(String benchmark);
  }
}
