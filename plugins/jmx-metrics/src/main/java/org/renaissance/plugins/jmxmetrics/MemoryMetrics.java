package org.renaissance.plugins.jmxmetrics;

import java.lang.management.MemoryMXBean;
import java.util.List;
import java.util.Objects;

import org.renaissance.plugins.jmxmetrics.Config.Token;

/** The overall heap and non-heap usage from {@link MemoryMXBean}. */
final class MemoryMetrics {
  private final MemoryMXBean bean;

  MemoryMetrics(MemoryMXBean bean) {
    this.bean = Objects.requireNonNull(bean);
  }

  List<Metric> create(Selection selection, String prefix) {
    return Metric.listOf(
      Metric.optionallyWithDelta(
        prefix + "heap_used_bytes",
        selection.contains(Token.USED),
        selection.contains(Token.USED, Token.DELTA),
        () -> Metric.usedOf(bean.getHeapMemoryUsage())
      ),
      Metric.optionallyWithDelta(
        prefix + "nonheap_used_bytes",
        selection.contains(Token.NONHEAP_USED),
        selection.contains(Token.NONHEAP_USED, Token.DELTA),
        () -> Metric.usedOf(bean.getNonHeapMemoryUsage())
      )
    );
  }
}
