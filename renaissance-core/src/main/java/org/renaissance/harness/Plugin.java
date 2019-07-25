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

  interface ValidResultListener {
    /**
     * Called when a benchmark produces a new (valid) result. Will be called
     * after completion of the measured benchmark operation, i.e., never inside
     * the measured code.
     *
     * @param benchmark Name of the benchmark.
     * @param metric Result name (e.g. branch-misses).
     * @param value Actual value of the metric.
     */
    void onValidResult(String benchmark, String metric, long value);
  }

  interface InvalidResultListener {
    /**
     * Called when a benchmark produces an invalid result. There will be
     * no more results for the given benchmark.
     *
     * @param benchmark Name of the benchmark.
     */
    void onInvalidResult(String benchmark);
  }
}
