package org.renaissance.plugins.jmxmetrics;

import org.renaissance.Plugin;

import java.lang.management.MemoryPoolMXBean;
import java.lang.management.ThreadMXBean;

/**
 * Parses plugin arguments into {@link Config}, builds a {@link MetricSet}
 * from it, and wires the result to {@link Plugin} entry points. The fields
 * are copied out of the {@link MetricSet} class to avoid extra indirection
 * in the per-operation methods below. No metrics are enabled by default, so
 * without at least one argument key, the plugin does not report anything.
 */
public final class Main implements Plugin,
    Plugin.AfterOperationSetUpListener,
    Plugin.BeforeOperationTearDownListener,
    Plugin.MeasurementResultPublisher {

  private final Metric[] metrics;
  private final Metric[] baseMetrics;
  private final Metric[] deltaMetrics;
  private final MemoryPoolMXBean[] resettableMemoryPoolBeans;
  private final ThreadMXBean resettableThreadBean;

  public Main(String... args) {
    MetricSet metricSet = MetricSet.from(Config.parse(args));

    metrics = metricSet.metrics;
    baseMetrics = metricSet.baseMetrics;
    deltaMetrics = metricSet.deltaMetrics;
    resettableMemoryPoolBeans = metricSet.resettableMemoryPoolBeans;
    resettableThreadBean = metricSet.resettableThreadBean;
  }

  @Override
  public void afterOperationSetUp(String benchmark, int opIndex, boolean isLastOp) {
    for (MemoryPoolMXBean bean : resettableMemoryPoolBeans) {
      bean.resetPeakUsage();
    }

    if (resettableThreadBean != null) {
      resettableThreadBean.resetPeakThreadCount();
    }

    for (Metric metric : deltaMetrics) {
      metric.sampleBefore();
    }
  }

  @Override
  public void beforeOperationTearDown(String benchmark, int opIndex, long harnessDuration) {
    for (Metric metric : metrics) {
      metric.sampleAfter();
    }
  }

  @Override
  public void onMeasurementResultsRequested(
    String benchmark, int opIndex, Plugin.MeasurementResultListener dispatcher
  ) {
    for (Metric metric : baseMetrics) {
      dispatcher.onMeasurementResult(benchmark, metric.baseName, metric.value());
    }

    for (Metric metric : deltaMetrics) {
      dispatcher.onMeasurementResult(benchmark, metric.deltaName, metric.delta());
    }
  }
}
