package org.renaissance;

public interface ResultObserver {

  /**
   * Called when a new result is obtained. Will be called after benchmark repetition is
   * completed, i.e. never inside the measured code.
   *
   * @param benchmark Name of the benchmark.
   * @param metric Result name (e.g. branch-misses).
   * @param value Actual value.
   */
  void onNewResult(String benchmark, String metric, long value);

  // TODO Plugins should register for benchmark life-cycle events separately
  void onExit();

}
