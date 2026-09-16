package org.renaissance.plugins.jmxmetrics;

import java.lang.management.GarbageCollectorMXBean;
import java.util.List;
import java.util.Objects;

import org.renaissance.plugins.jmxmetrics.Config.Token;

import static java.util.stream.Collectors.toList;

/** Per-collector GC metrics from {@link GarbageCollectorMXBean}. */
final class GarbageCollectorMetrics {
  private final List<GarbageCollectorMXBean> beans;

  GarbageCollectorMetrics(List<GarbageCollectorMXBean> beans) {
    this.beans = Objects.requireNonNull(beans);
  }

  List<Metric> create(Selection selection, String prefix) {
    return beans.stream()
      .flatMap(bean -> {
        String base = prefix + Metric.sanitize(bean.getName());
        return Metric.streamOf(
          Metric.optionallyWithDelta(
            base + "_collection_count",
            selection.contains(Token.COUNT),
            selection.contains(Token.COUNT, Token.DELTA),
            bean::getCollectionCount
          ),
          Metric.optionallyWithDelta(
            base + "_collection_time_ms",
            selection.contains(Token.TIME),
            selection.contains(Token.TIME, Token.DELTA),
            bean::getCollectionTime
          )
        );
      }).collect(toList());
  }
}
