package org.renaissance;

import org.renaissance.harness.Plugin.*;

/**
 * Helper class to dispatch events to listeners. Uses array iteration to
 * avoid creating iteration objects.
 */
final class EventDispatcher {
  private final HarnessInitListener[] harnessInitListeners;
  private final HarnessShutdownListener[] harnessShutdownListeners;
  private final BenchmarkSetUpListener[] benchmarkSetUpListeners;
  private final BenchmarkTearDownListener[] benchmarkTearDownListeners;
  private final OperationSetUpListener[] operationSetUpListeners;
  private final OperationTearDownListener[] operationTearDownListeners;
  private final BenchmarkResultListener[] benchmarkResultListeners;
  private final BenchmarkFailureListener[] benchmarkFailureListeners;


  EventDispatcher(Config config) {
    harnessInitListeners = config.harnessInitListeners.toArray(
      new HarnessInitListener[0]
    );

    harnessShutdownListeners = config.harnessShutdownListeners.toArray(
      new HarnessShutdownListener[0]
    );

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

    benchmarkResultListeners = config.benchmarkResultListeners.toArray(
      new BenchmarkResultListener[0]
    );

    benchmarkFailureListeners = config.benchmarkFailureListeners.toArray(
      new BenchmarkFailureListener[0]
    );
  }

  //
  // TODO: Handle exceptions gracefully, indicating the listener which caused it.
  //

  void notifyAfterHarnessInit() {
    for (final HarnessInitListener l : harnessInitListeners) {
      l.afterHarnessInit();
    }
  }


  void notifyBeforeHarnessShutdown() {
    for (final HarnessShutdownListener l : harnessShutdownListeners) {
      l.beforeHarnessShutdown();
    }
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
    final String benchName, final int opIndex, final boolean isLastOp
  ) {
    for (final OperationSetUpListener l : operationSetUpListeners) {
      l.afterOperationSetUp(benchName, opIndex, isLastOp);
    }
  }


  void notifyBeforeOperationTearDown(
    final String benchName, final int opIndex, long durationNanos
  ) {
    for (final OperationTearDownListener l : operationTearDownListeners) {
      l.beforeOperationTearDown(benchName, opIndex, durationNanos);
    }
  }


  void notifyOnBenchmarkResult(
    final String benchName, final String metric, final long value
  ) {
    for (final BenchmarkResultListener l : benchmarkResultListeners) {
      l.onBenchmarkResult(benchName, metric, value);
    }
  }


  void notifyOnBenchmarkFailure(final String benchName) {
    for (final BenchmarkFailureListener l : benchmarkFailureListeners) {
      l.onBenchmarkFailure(benchName);
    }
  }

}
