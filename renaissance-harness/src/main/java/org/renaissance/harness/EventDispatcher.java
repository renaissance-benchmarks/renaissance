package org.renaissance.harness;

import org.renaissance.Plugin;
import org.renaissance.Plugin.AfterBenchmarkSetUpListener;
import org.renaissance.Plugin.AfterBenchmarkTearDownListener;
import org.renaissance.Plugin.AfterHarnessInitListener;
import org.renaissance.Plugin.AfterOperationSetUpListener;
import org.renaissance.Plugin.BeforeBenchmarkSetUpListener;
import org.renaissance.Plugin.BeforeBenchmarkTearDownListener;
import org.renaissance.Plugin.BeforeHarnessShutdownListener;
import org.renaissance.Plugin.BeforeOperationTearDownListener;
import org.renaissance.Plugin.BenchmarkFailureListener;
import org.renaissance.Plugin.MeasurementResultListener;
import org.renaissance.Plugin.MeasurementResultPublisher;

import java.util.ArrayList;
import java.util.List;

/**
 * Helper class to dispatch events to listeners. This may seem a bit more
 * complicated than strictly necessary, however the goal is to iterate over
 * arrays, without any indirection associated with getting elements from an
 * array list, and without triggering creation of auxiliary iteration objects
 * due to use of for-each.
 */
final class EventDispatcher {

  private final AfterHarnessInitListener[] afterHarnessInitListeners;
  private final BeforeHarnessShutdownListener[] beforeHarnessShutdownListeners;

  private final BeforeBenchmarkSetUpListener[] beforeBenchmarkSetUpListeners;
  private final AfterBenchmarkTearDownListener[] afterBenchmarkTearDownListeners;

  private final AfterBenchmarkSetUpListener[] afterBenchmarkSetUpListeners;
  private final BeforeBenchmarkTearDownListener[] beforeBenchmarkTearDownListeners;

  private final AfterOperationSetUpListener[] afterOperationSetUpListeners;
  private final BeforeOperationTearDownListener[] beforeOperationTearDownListeners;

  private final MeasurementResultListener[] measurementResultListeners;
  private final BenchmarkFailureListener[] benchmarkFailureListeners;
  private final MeasurementResultPublisher[] measurementResultPublishers;


  private EventDispatcher(Builder builder) {
    afterHarnessInitListeners = builder.afterHarnessInitListeners.toArray(new AfterHarnessInitListener[0]);
    beforeHarnessShutdownListeners = builder.beforeHarnessShutdownListeners.toArray(new BeforeHarnessShutdownListener[0]);

    beforeBenchmarkSetUpListeners = builder.beforeBenchmarkSetUpListeners.toArray(new BeforeBenchmarkSetUpListener[0]);
    afterBenchmarkTearDownListeners = builder.afterBenchmarkTearDownListeners.toArray(new AfterBenchmarkTearDownListener[0]);

    afterBenchmarkSetUpListeners = builder.afterBenchmarkSetUpListeners.toArray(new AfterBenchmarkSetUpListener[0]);
    beforeBenchmarkTearDownListeners = builder.beforeBenchmarkTearDownListeners.toArray(new BeforeBenchmarkTearDownListener[0]);

    afterOperationSetUpListeners = builder.afterOperationSetUpListeners.toArray(new AfterOperationSetUpListener[0]);
    beforeOperationTearDownListeners = builder.beforeOperationTearDownListeners.toArray(new BeforeOperationTearDownListener[0]);

    measurementResultListeners = builder.measurementResultListeners.toArray(new MeasurementResultListener[0]);
    measurementResultPublishers = builder.measurementResultPublishers.toArray(new MeasurementResultPublisher[0]);

    benchmarkFailureListeners = builder.benchmarkFailureListeners.toArray(new BenchmarkFailureListener[0]);
  }

  //
  // TODO: Handle exceptions gracefully, indicating the listener which caused it.
  //

  void notifyAfterHarnessInit() {
    for (final AfterHarnessInitListener l : afterHarnessInitListeners) {
      l.afterHarnessInit();
    }
  }

  void notifyBeforeHarnessShutdown() {
    for (final BeforeHarnessShutdownListener l : beforeHarnessShutdownListeners) {
      l.beforeHarnessShutdown();
    }
  }


  void notifyBeforeBenchmarkSetUp(final String benchName) {
    for (final BeforeBenchmarkSetUpListener l : beforeBenchmarkSetUpListeners) {
      l.beforeBenchmarkSetUp(benchName);
    }
  }

  void notifyAfterBenchmarkTearDown(final String benchName) {
    for (final AfterBenchmarkTearDownListener l : afterBenchmarkTearDownListeners) {
      l.afterBenchmarkTearDown(benchName);
    }
  }


  void notifyAfterBenchmarkSetUp(final String benchName) {
    for (final AfterBenchmarkSetUpListener l : afterBenchmarkSetUpListeners) {
      l.afterBenchmarkSetUp(benchName);
    }
  }

  void notifyBeforeBenchmarkTearDown(final String benchName) {
    for (final BeforeBenchmarkTearDownListener l : beforeBenchmarkTearDownListeners) {
      l.beforeBenchmarkTearDown(benchName);
    }
  }


  void notifyAfterOperationSetUp(
    final String benchName, final int opIndex, final boolean isLastOp
  ) {
    for (final AfterOperationSetUpListener l : afterOperationSetUpListeners) {
      l.afterOperationSetUp(benchName, opIndex, isLastOp);
    }
  }

  void notifyBeforeOperationTearDown(
    final String benchName, final int opIndex, final long durationNanos
  ) {
    for (final BeforeOperationTearDownListener l : beforeOperationTearDownListeners) {
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
    private final List<AfterHarnessInitListener> afterHarnessInitListeners = new ArrayList<>();
    private final List<BeforeHarnessShutdownListener> beforeHarnessShutdownListeners = new ArrayList<>();

    private final List<BeforeBenchmarkSetUpListener> beforeBenchmarkSetUpListeners = new ArrayList<>();
    private final List<AfterBenchmarkTearDownListener> afterBenchmarkTearDownListeners = new ArrayList<>();

    private final List<AfterBenchmarkSetUpListener> afterBenchmarkSetUpListeners = new ArrayList<>();
    private final List<BeforeBenchmarkTearDownListener> beforeBenchmarkTearDownListeners = new ArrayList<>();

    private final List<AfterOperationSetUpListener> afterOperationSetUpListeners = new ArrayList<>();
    private final List<BeforeOperationTearDownListener> beforeOperationTearDownListeners = new ArrayList<>();

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
      appendInstanceOf(plugin, AfterHarnessInitListener.class, afterHarnessInitListeners);
      prependInstanceOf(plugin, BeforeHarnessShutdownListener.class, beforeHarnessShutdownListeners);

      appendInstanceOf(plugin, BeforeBenchmarkSetUpListener.class, beforeBenchmarkSetUpListeners);
      prependInstanceOf(plugin, AfterBenchmarkTearDownListener.class, afterBenchmarkTearDownListeners);

      appendInstanceOf(plugin, AfterBenchmarkSetUpListener.class, afterBenchmarkSetUpListeners);
      prependInstanceOf(plugin, BeforeBenchmarkTearDownListener.class, beforeBenchmarkTearDownListeners);

      appendInstanceOf(plugin, AfterOperationSetUpListener.class, afterOperationSetUpListeners);
      prependInstanceOf(plugin, BeforeOperationTearDownListener.class, beforeOperationTearDownListeners);

      appendInstanceOf(plugin, MeasurementResultListener.class, measurementResultListeners);
      appendInstanceOf(plugin, MeasurementResultPublisher.class, measurementResultPublishers);

      appendInstanceOf(plugin, BenchmarkFailureListener.class, benchmarkFailureListeners);
      return this;
    }

    private static <T extends Plugin> void prependInstanceOf(
      Plugin plugin, Class<T> listenerType, List<T> listeners
    ) {
      if (listenerType.isInstance(plugin)) {
        listeners.add(0, listenerType.cast(plugin));
      }
    }

    private static <T extends Plugin> void appendInstanceOf(
      Plugin plugin, Class<T> listenerType, List<T> listeners
    ) {
      if (listenerType.isInstance(plugin)) {
        listeners.add(listenerType.cast(plugin));
      }
    }

    /**
     * Registers a {@link ResultWriter} into respective listener lists.
     *
     * @param writer The {@link ResultWriter} to register.
     * @return This {@link Builder}.
     */
    public Builder withResultWriter(ResultWriter writer) {
      beforeHarnessShutdownListeners.add(writer);
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
