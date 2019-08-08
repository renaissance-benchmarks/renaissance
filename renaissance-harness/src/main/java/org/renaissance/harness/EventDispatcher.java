package org.renaissance.harness;

import org.renaissance.Plugin;
import org.renaissance.Plugin.*;

import java.util.ArrayList;
import java.util.List;

/**
 * Helper class to dispatch events to listeners. This may seem a bit more complicated
 * than strictly necessary, however the goal is to iterate over arrays, without any
 * indirection associated with getting elements from an array list, and without triggering
 * creation of auxiliary iteration objects due to use of for-each.
 */
final class EventDispatcher {

  private final HarnessInitListener[] harnessInitListeners;
  private final HarnessShutdownListener[] harnessShutdownListeners;
  private final BenchmarkSetUpListener[] benchmarkSetUpListeners;
  private final BenchmarkTearDownListener[] benchmarkTearDownListeners;
  private final OperationSetUpListener[] operationSetUpListeners;
  private final OperationTearDownListener[] operationTearDownListeners;
  private final MeasurementResultListener[] measurementResultListeners;
  private final BenchmarkFailureListener[] benchmarkFailureListeners;
  private final MeasurementResultPublisher[] measurementResultPublishers;


  private EventDispatcher(Builder builder) {
    harnessInitListeners = builder.harnessInitListeners.toArray(new HarnessInitListener[0]);
    harnessShutdownListeners = builder.harnessShutdownListeners.toArray(new HarnessShutdownListener[0]);
    benchmarkSetUpListeners = builder.benchmarkSetUpListeners.toArray(new BenchmarkSetUpListener[0]);
    benchmarkTearDownListeners = builder.benchmarkTearDownListeners.toArray(new BenchmarkTearDownListener[0]);
    operationSetUpListeners = builder.operationSetUpListeners.toArray(new OperationSetUpListener[0]);
    operationTearDownListeners = builder.operationTearDownListeners.toArray(new OperationTearDownListener[0]);
    measurementResultListeners = builder.measurementResultListeners.toArray(new MeasurementResultListener[0]);
    measurementResultPublishers = builder.measurementResultPublishers.toArray(new MeasurementResultPublisher[0]);
    benchmarkFailureListeners = builder.benchmarkFailureListeners.toArray(new BenchmarkFailureListener[0]);
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
    final String benchName, final int opIndex, final long durationNanos
  ) {
    for (final OperationTearDownListener l : operationTearDownListeners) {
      l.beforeOperationTearDown(benchName, opIndex, durationNanos);
    }
  }


  void notifyOnMeasurementResult(
    final String benchName, final String metric, final long value
  ) {
    for (final MeasurementResultListener l : measurementResultListeners) {
      l.onMeasurementResult(benchName, metric, value);
    }
  }

  void notifyOnMeasurementResultsRequested(
    final String benchName, final int opIndex, final MeasurementResultListener dispatcher
  ) {
    for (final MeasurementResultPublisher l : measurementResultPublishers) {
      l.onMeasurementResultsRequested(benchName, opIndex, dispatcher);
    }
  }


  void notifyOnBenchmarkFailure(final String benchName) {
    for (final BenchmarkFailureListener l : benchmarkFailureListeners) {
      l.onBenchmarkFailure(benchName);
    }
  }

  //

  static final class Builder {
    private final List<HarnessInitListener> harnessInitListeners = new ArrayList<>();
    private final List<HarnessShutdownListener> harnessShutdownListeners = new ArrayList<>();
    private final List<BenchmarkSetUpListener> benchmarkSetUpListeners = new ArrayList<>();
    private final List<BenchmarkTearDownListener> benchmarkTearDownListeners = new ArrayList<>();
    private final List<OperationSetUpListener> operationSetUpListeners = new ArrayList<>();
    private final List<OperationTearDownListener> operationTearDownListeners = new ArrayList<>();
    private final List<MeasurementResultListener> measurementResultListeners = new ArrayList<>();
    private final List<MeasurementResultPublisher> measurementResultPublishers = new ArrayList<>();
    private final List<BenchmarkFailureListener> benchmarkFailureListeners = new ArrayList<>();

    /**
     * Registers a plugin into listener lists based on implemented interfaces.
     * Note that pair events (setup and teardown) are added to opposite
     * ends of the lists so that each plugin can wrap existing plugins.
     * <p>
     * Therefore it is expected that measurement plugins would be added
     * as the last ones on the command-line.
     *
     * @param plugin The {@link Plugin} to register
     * @return This {@link Builder}.
     */
    public Builder withPlugin(Plugin plugin) {
      if (plugin instanceof HarnessInitListener) {
        harnessInitListeners.add((HarnessInitListener) plugin);
      }
      if (plugin instanceof HarnessShutdownListener) {
        harnessShutdownListeners.add(0, (HarnessShutdownListener) plugin);
      }

      if (plugin instanceof BenchmarkSetUpListener) {
        benchmarkSetUpListeners.add((BenchmarkSetUpListener) plugin);
      }
      if (plugin instanceof BenchmarkTearDownListener) {
        benchmarkTearDownListeners.add(0, (BenchmarkTearDownListener) plugin);
      }

      if (plugin instanceof OperationSetUpListener) {
        operationSetUpListeners.add((OperationSetUpListener) plugin);
      }
      if (plugin instanceof OperationTearDownListener) {
        operationTearDownListeners.add(0, (OperationTearDownListener) plugin);
      }

      if (plugin instanceof MeasurementResultListener) {
        measurementResultListeners.add((MeasurementResultListener) plugin);
      }
      if (plugin instanceof MeasurementResultPublisher) {
        measurementResultPublishers.add((MeasurementResultPublisher) plugin);
      }

      if (plugin instanceof BenchmarkFailureListener) {
        benchmarkFailureListeners.add((BenchmarkFailureListener) plugin);
      }

      return this;
    }


    /**
     * Registers a {@link ResultWriter} into respective listener lists.
     *
     * @param writer The {@link ResultWriter} to register.
     * @return This {@link Builder}.
     */
    public Builder withResultWriter(ResultWriter writer) {
      harnessShutdownListeners.add(writer);
      measurementResultListeners.add(writer);
      benchmarkFailureListeners.add(writer);
      return this;
    }


    /**
     * @return A new instance of {@link EventDispatcher}.
     */
    public EventDispatcher build() {
      return new EventDispatcher(this);
    }
  }

}
