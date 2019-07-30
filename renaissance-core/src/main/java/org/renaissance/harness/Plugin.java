package org.renaissance.harness;

/**
 *  Plugin implementations must have a zero arguments constructor.
 */
public interface Plugin {
  interface HarnessInitListener {
    void afterHarnessInit();
  }

  interface HarnessShutdownListener {
    void beforeHarnessShutdown();
  }

  interface BenchmarkSetUpListener {
    void afterBenchmarkSetUp(String benchmark);
  }

  interface BenchmarkTearDownListener {
    void beforeBenchmarkTearDown(String benchmark);
  }

  interface OperationSetUpListener {
    void afterOperationSetUp(String benchmark, int opIndex, boolean isLastOp);
  }

  interface OperationTearDownListener {
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
     * Called whenever a benchmark fails during set up, tear down, or
     * operation (including operation set up and tear down). There will be
     * no more results for the given benchmark after this event.
     *
     * @param benchmark Name of the benchmark.
     */
    void onBenchmarkFailure(String benchmark);
  }
}
