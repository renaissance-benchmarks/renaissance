package org.renaissance.harness;

import java.util.function.ToIntFunction;

import static org.renaissance.Plugin.AfterBenchmarkSetUpListener;
import static org.renaissance.Plugin.BeforeOperationTearDownListener;
import static org.renaissance.Plugin.ExecutionPolicy;

/**
 * A collection of (simple) execution policies.
 */
final class ExecutionPolicies {

  /**
   * Executes a benchmark's measured operation for a given number of times.
   * The number of repetitions can be specific to each benchmark, therefore
   * the policy needs to be provided with a function that returns the number
   * of repetitions for a given benchmark.
   */
  static final class FixedOpCount implements ExecutionPolicy,
    AfterBenchmarkSetUpListener {

    private final ToIntFunction<String> countLimitProvider;

    private int countLimit;

    FixedOpCount(ToIntFunction<String> countLimitProvider) {
      this.countLimitProvider = countLimitProvider;
    }

    @Override
    public void afterBenchmarkSetUp(String benchName) {
      // Reset counters for each benchmark
      countLimit = countLimitProvider.applyAsInt(benchName);
    }

    @Override
    public boolean canExecute(String benchmark, int opIndex) {
      return opIndex < countLimit;
    }

    @Override
    public boolean isLast(String benchmark, int opIndex) {
      return opIndex + 1 == countLimit;
    }
  }


  /**
   * Keeps executing the benchmark's measured operation for a fixed amount
   * of time. The interval starts after a benchmark has been set up, before
   * the first execution of a benchmark's measured operation.
   * <p>
   * Note that the timer interval also includes the time consumed by other
   * plugins and event listeners.
   */
  static final class FixedTime implements ExecutionPolicy,
    AfterBenchmarkSetUpListener, BeforeOperationTearDownListener {

    private final long runTimeNanos;

    private long endNanos;
    private int elapsedCount;

    FixedTime(final long runTimeNanos) {
      this.runTimeNanos = runTimeNanos;
    }

    @Override
    public void afterBenchmarkSetUp(String benchmark) {
      // Reset counters for each benchmark
      endNanos = System.nanoTime() + runTimeNanos;
      elapsedCount = 0;
    }

    @Override
    public void beforeOperationTearDown(String benchmark, int opIndex, long durationNanos) {
      elapsedCount += (System.nanoTime() >= endNanos) ? 1 : 0;
    }

    @Override
    public boolean canExecute(String benchmark, int opIndex) {
      return elapsedCount <= 1;
    }

    @Override
    public boolean isLast(String benchmark, int opIndex) {
      return elapsedCount == 1;
    }
  }


  /**
   * Keeps executing the benchmark's measured operation until the accumulated
   * execution time of the operation exceeds a given limit. This policy differs
   * from the {@link FixedTime} policy in that it does not include the execution
   * time of other plugins and event listeners.
   */
  static final class FixedOpTime implements ExecutionPolicy,
    AfterBenchmarkSetUpListener, BeforeOperationTearDownListener {

    private final long operationRunTimeNanos;

    private long remainingNanos;
    private int elapsedCount;

    FixedOpTime(final long operationRunTimeNanos) {
      this.operationRunTimeNanos = operationRunTimeNanos;
    }

    @Override
    public void afterBenchmarkSetUp(String benchmark) {
      // Reset counters for each benchmark
      remainingNanos = operationRunTimeNanos;
      elapsedCount = 0;
    }

    @Override
    public void beforeOperationTearDown(String benchmark, int opIndex, long durationNanos) {
      remainingNanos -= durationNanos;
      elapsedCount += (remainingNanos <= 0) ? 1 : 0;
    }

    @Override
    public boolean canExecute(String benchmark, int opIndex) {
      return elapsedCount <= 1;
    }

    @Override
    public boolean isLast(String benchmark, int opIndex) {
      return elapsedCount == 1;
    }
  }

}
