package org.renaissance.plugins.jmxmetrics;

import java.lang.management.ClassLoadingMXBean;
import java.util.List;
import java.util.Objects;

import org.renaissance.plugins.jmxmetrics.Config.Token;

/**
 * Class loading metrics from {@link ClassLoadingMXBean}: the number of
 * classes currently loaded (a live count that can move in either direction)
 * and the cumulative totals of classes loaded and unloaded since JVM start.
 */
final class ClassLoadingMetrics {
  private final ClassLoadingMXBean bean;

  ClassLoadingMetrics(ClassLoadingMXBean bean) {
    this.bean = Objects.requireNonNull(bean);
  }

  List<Metric> create(Selection selection, String prefix) {
    return Metric.listOf(
      Metric.optionallyWithDelta(
        prefix + "live_count",
        selection.contains(Token.LIVE_COUNT),
        selection.contains(Token.LIVE_COUNT, Token.DELTA),
        bean::getLoadedClassCount
      ),
      Metric.optionallyWithDelta(
        prefix + "total_loaded_count",
        selection.contains(Token.TOTAL_LOADED_COUNT),
        selection.contains(Token.TOTAL_LOADED_COUNT, Token.DELTA),
        bean::getTotalLoadedClassCount
      ),
      Metric.optionallyWithDelta(
        prefix + "total_unloaded_count",
        selection.contains(Token.TOTAL_UNLOADED_COUNT),
        selection.contains(Token.TOTAL_UNLOADED_COUNT, Token.DELTA),
        bean::getUnloadedClassCount
      )
    );
  }
}
