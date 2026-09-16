package org.renaissance.plugins.jmxmetrics;

import java.lang.management.RuntimeMXBean;
import java.util.List;
import java.util.Objects;

import org.renaissance.plugins.jmxmetrics.Config.Token;

/** JVM start time and uptime from {@link RuntimeMXBean}. */
final class RuntimeMetrics {
  private final RuntimeMXBean bean;

  RuntimeMetrics(RuntimeMXBean bean) {
    this.bean = Objects.requireNonNull(bean);
  }

  List<Metric> create(Selection selection, String prefix) {
    return Metric.listOf(
      Metric.optionallyWithDelta(
        prefix + "vm_start_time_ms",
        selection.contains(Token.VM_START_TIME),
        selection.contains(Token.VM_START_TIME, Token.DELTA),
        bean::getStartTime
      ),
      Metric.optionallyWithDelta(
        prefix + "vm_uptime_ms",
        selection.contains(Token.VM_UPTIME),
        selection.contains(Token.VM_UPTIME, Token.DELTA),
        bean::getUptime
      )
    );
  }
}
