package org.renaissance.harness;

public interface ExecutionPolicy {

  /**
   * @return {@code true} if the harness should keep executing the
   * benchmark's measured operation, {@code false} otherwise.
   */
  boolean keepExecuting();

  /**
   * Notifies the policy that the benchmark's measured operation has
   * been executed one more time.
   *
   * @parem index the index of the measured operation
   * @param durationNanos the duration of the measured operation in nanoseconds.
   */
  void registerOperation(int index, long durationNanos);

  /**
   * @return {@code true} if the last operation is executing, {@code false}
   * otherwise (the policy might not know).
   */
  boolean isLastOperation();

}
