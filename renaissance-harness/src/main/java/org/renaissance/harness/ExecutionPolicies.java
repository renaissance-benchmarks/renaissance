package org.renaissance.harness;

import org.renaissance.ExecutionPolicy;

/**
 * A collection of (simple) execution policies.
 */
final class ExecutionPolicies {

  static ExecutionPolicy fixedCount(final int count) {
    return new ExecutionPolicy() {
      private int executedCount = 0;

      @Override
      public boolean keepExecuting() {
        return executedCount < count;
      }

      @Override
      public void registerOperation(int index, long duration) {
        executedCount = index + 1;
      }

      @Override
      public boolean isLastOperation() { return executedCount + 1 >= count; }
    };
  }

  static ExecutionPolicy fixedTime(long elapsedNanosLimit) {
    return new ExecutionPolicy() {
      private long lastNanos = -1;
      private long elapsedNanos = 0;
      private int elapsedCount = 0;

      @Override
      public boolean keepExecuting() { return !isElapsed() || isLastOperation(); }

      private boolean isElapsed() { return elapsedNanos >= elapsedNanosLimit; }

      @Override
      public void registerOperation(int index, long durationNanos) {
        final long currentNanos = System.nanoTime();

        if (lastNanos < 0) {
          lastNanos = currentNanos - durationNanos;
        }

        elapsedNanos += currentNanos - lastNanos;
        elapsedCount += isElapsed() ? 1 : 0;
      }

      @Override
      public boolean isLastOperation() { return elapsedCount == 1; }
    };
  }

  static ExecutionPolicy fixedOperationTime(long elapsedNanosLimit) {
    return new ExecutionPolicy() {
      private long elapsedNanos = 0;
      private int elapsedCount = 0;

      @Override
      public boolean keepExecuting() { return !isElapsed() || isLastOperation(); }

      private boolean isElapsed() { return elapsedNanos >= elapsedNanosLimit; }

      @Override
      public void registerOperation(int index, long durationNanos) {
        elapsedNanos += durationNanos;
        elapsedCount += isElapsed() ? 1 : 0;
      }

      @Override
      public boolean isLastOperation() { return elapsedCount == 1; }
    };
  }

}
