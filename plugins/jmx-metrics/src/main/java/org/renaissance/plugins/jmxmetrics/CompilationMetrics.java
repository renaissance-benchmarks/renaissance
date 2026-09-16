package org.renaissance.plugins.jmxmetrics;

import java.lang.management.CompilationMXBean;
import java.util.List;

import org.renaissance.plugins.jmxmetrics.Config.Token;

import static java.util.Collections.emptyList;
import static org.renaissance.plugins.jmxmetrics.MetricSet.warn;

/** Total JIT compilation time from {@link CompilationMXBean}. */
final class CompilationMetrics {
  private final CompilationMXBean bean; // nullable: not every JVM has a compilation system

  CompilationMetrics(CompilationMXBean bean) {
    this.bean = bean;
  }

  List<Metric> create(Selection selection, String prefix) {
    if (!selection.containsAnyOf(Token.TIME)) {
      return emptyList();
    }

    if (bean == null) {
      warn("This JVM does not have a compilation system that could be monitored.");
      return emptyList();
    }

    if (!bean.isCompilationTimeMonitoringSupported()) {
      warn("This JVM does not support compilation time monitoring.");
      return emptyList();
    }

    return Metric.listOf(
      Metric.optionallyWithDelta(
        prefix + "total_compilation_time_ms",
        selection.contains(Token.TIME),
        selection.contains(Token.TIME, Token.DELTA),
        bean::getTotalCompilationTime
      )
    );
  }
}
