package org.renaissance;

public interface ResultObserver {
  /** Callback when new result is obtained.
   *
   * Will be called after iteration is completed, i.e. never inside measured
   * loop.
   *
   * @param benchmark Name of the benchmark.
   * @param metric Result name (e.g. branch-misses).
   * @param value Actual value.
   */
  public void onNewResult(String benchmark, String metric, long value);
  public void onExit();
}
