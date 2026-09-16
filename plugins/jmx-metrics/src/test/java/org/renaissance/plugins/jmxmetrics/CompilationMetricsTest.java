package org.renaissance.plugins.jmxmetrics;

import org.junit.jupiter.api.Test;

import javax.management.ObjectName;
import java.lang.management.CompilationMXBean;
import java.util.List;

import org.renaissance.plugins.jmxmetrics.Config.Key;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Covers the paths {@link MainMetricNamesTest} cannot reach portably: no
 * compilation system at all, or one that does not support time monitoring.
 * Both depend on what the real JVM happens to provide, so they are tested
 * here against a fake instead.
 */
class CompilationMetricsTest {

  private static CompilationMXBean fakeCompilationBean(boolean supported, long totalTime) {
    return new CompilationMXBean() {
      @Override public String getName() { return "fake"; }
      @Override public boolean isCompilationTimeMonitoringSupported() { return supported; }
      @Override public long getTotalCompilationTime() { return totalTime; }
      @Override public ObjectName getObjectName() { return null; }
    };
  }

  @Test
  void nothingSelectedSkipsTheBeanEntirely() {
    // 'time' not selected: must not even look at the (here null) bean.
    List<Metric> metrics = new CompilationMetrics(null).create(Selection.empty(Key.JIT), "jmx_jit_");

    assertTrue(metrics.isEmpty());
  }

  @Test
  void nullBeanReportsNothing() {
    List<Metric> metrics = new CompilationMetrics(null)
      .create(Selection.parse(Key.JIT, "time"), "jmx_jit_");

    assertTrue(metrics.isEmpty());
  }

  @Test
  void unsupportedBeanReportsNothing() {
    CompilationMXBean bean = fakeCompilationBean(false, 123);
    List<Metric> metrics = new CompilationMetrics(bean)
      .create(Selection.parse(Key.JIT, "time"), "jmx_jit_");

    assertTrue(metrics.isEmpty());
  }

  @Test
  void supportedBeanReportsBothNames() {
    CompilationMXBean bean = fakeCompilationBean(true, 123);
    List<Metric> metrics = new CompilationMetrics(bean)
      .create(Selection.parse(Key.JIT, "time@both"), "jmx_jit_");

    assertEquals(1, metrics.size());
    assertEquals("jmx_jit_total_compilation_time_ms", metrics.get(0).baseName);
    assertEquals("jmx_jit_total_compilation_time_ms_delta", metrics.get(0).deltaName);
  }
}
