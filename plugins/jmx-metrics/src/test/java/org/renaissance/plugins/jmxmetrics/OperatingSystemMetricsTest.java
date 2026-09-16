package org.renaissance.plugins.jmxmetrics;

import org.junit.jupiter.api.Test;

import javax.management.ObjectName;
import java.lang.management.OperatingSystemMXBean;
import java.util.List;
import java.util.Set;

import org.renaissance.plugins.jmxmetrics.Config.Key;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Covers the paths the {@link MainMetricNamesTest} cannot reach portably: no
 * operating-system bean at all, or one that does not implement the
 * platform-specific extended interface. Both depend on what the real JVM
 * happens to provide, so they are tested against fakes instead.
 */
class OperatingSystemMetricsTest {

  /** A plain, portable-only bean -- deliberately not the extended interface. */
  private static OperatingSystemMXBean fakePortableBean(double loadAverage, int processors) {
    return new OperatingSystemMXBean() {
      @Override public String getName() { return "fake"; }
      @Override public String getArch() { return "fake"; }
      @Override public String getVersion() { return "fake"; }
      @Override public int getAvailableProcessors() { return processors; }
      @Override public double getSystemLoadAverage() { return loadAverage; }
      @Override public ObjectName getObjectName() { return null; }
    };
  }

  private static com.sun.management.OperatingSystemMXBean fakeExtendedBean(
    double loadAverage, int processors, double systemCpuLoad, double processCpuLoad, long processCpuTime
  ) {
    return new com.sun.management.OperatingSystemMXBean() {
      @Override public String getName() { return "fake"; }
      @Override public String getArch() { return "fake"; }
      @Override public String getVersion() { return "fake"; }
      @Override public int getAvailableProcessors() { return processors; }
      @Override public double getSystemLoadAverage() { return loadAverage; }
      @Override public ObjectName getObjectName() { return null; }
      @Override public long getCommittedVirtualMemorySize() { return 0; }
      @Override public long getTotalSwapSpaceSize() { return 0; }
      @Override public long getFreeSwapSpaceSize() { return 0; }
      @Override public long getProcessCpuTime() { return processCpuTime; }
      @Override public long getFreePhysicalMemorySize() { return 0; }
      @Override public long getTotalPhysicalMemorySize() { return 0; }
      @Override public double getSystemCpuLoad() { return systemCpuLoad; }
      @Override public double getProcessCpuLoad() { return processCpuLoad; }
    };
  }

  @Test
  void nullBeanReportsNothing() {
    List<Metric> metrics = new OperatingSystemMetrics(null)
      .create(Selection.parse(Key.OS, "all"), "jmx_os_");

    assertTrue(metrics.isEmpty());
  }

  @Test
  void nonExtendedBeanReportsOnlyPortableMetrics() {
    OperatingSystemMXBean bean = fakePortableBean(2.34, 16);
    List<Metric> metrics = new OperatingSystemMetrics(bean)
      .create(Selection.parse(Key.OS, "all"), "jmx_os_");

    Set<String> names = metrics.stream().map(m -> m.baseName).collect(java.util.stream.Collectors.toSet());
    assertTrue(names.contains("jmx_os_system_load_average_x100"));
    assertTrue(names.contains("jmx_os_available_processors_count"));
    assertFalse(names.contains("jmx_os_system_cpu_load_mpct"));
    assertFalse(names.contains("jmx_os_process_cpu_load_mpct"));
    assertFalse(names.contains("jmx_os_process_cpu_time_ns"));
  }

  @Test
  void extendedBeanReportsAllFiveMetrics() {
    com.sun.management.OperatingSystemMXBean bean =
      fakeExtendedBean(2.34, 16, 0.3712, 0.0612, 48123456789L);
    List<Metric> metrics = new OperatingSystemMetrics(bean)
      .create(Selection.parse(Key.OS, "all"), "jmx_os_");

    Set<String> names = metrics.stream().map(m -> m.baseName).collect(java.util.stream.Collectors.toSet());
    assertEquals(
      Set.of(
        "jmx_os_system_load_average_x100", "jmx_os_available_processors_count",
        "jmx_os_system_cpu_load_mpct", "jmx_os_process_cpu_load_mpct", "jmx_os_process_cpu_time_ns"
      ),
      names
    );
  }

  @Test
  void loadAverageIsScaledByOneHundred() {
    com.sun.management.OperatingSystemMXBean bean = fakeExtendedBean(2.34, 16, 0, 0, 0);
    List<Metric> metrics = new OperatingSystemMetrics(bean)
      .create(Selection.parse(Key.OS, "load-average"), "jmx_os_");

    metrics.get(0).sampleAfter();
    assertEquals(234L, metrics.get(0).value());
  }

  @Test
  void negativeLoadAverageSentinelIsPreservedNotScaled() {
    // getSystemLoadAverage() returns -1 when unavailable on this platform;
    // that must come through as -1, not as -100.
    com.sun.management.OperatingSystemMXBean bean = fakeExtendedBean(-1, 16, 0, 0, 0);
    List<Metric> metrics = new OperatingSystemMetrics(bean)
      .create(Selection.parse(Key.OS, "load-average"), "jmx_os_");

    metrics.get(0).sampleAfter();
    assertEquals(-1L, metrics.get(0).value());
  }

  @Test
  void systemCpuLoadIsScaledToMilliPercent() {
    com.sun.management.OperatingSystemMXBean bean = fakeExtendedBean(0, 16, 0.3712, 0, 0);
    List<Metric> metrics = new OperatingSystemMetrics(bean)
      .create(Selection.parse(Key.OS, "system-load"), "jmx_os_");

    metrics.get(0).sampleAfter();
    assertEquals(37120L, metrics.get(0).value());
  }
}
