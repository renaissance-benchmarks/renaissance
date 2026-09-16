package org.renaissance.plugins.jmxmetrics;

import org.junit.jupiter.api.Test;

import java.lang.management.ManagementFactory;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assumptions.assumeTrue;

/**
 * Integration-level tests constructing the real plugin and driving the
 * actual {@link org.renaissance.Plugin} lifecycle. These check which metric
 * *names* get published, not their values: GC counts, compilation time, and
 * whether thread-allocated-bytes is available at all are legitimately
 * JVM/vendor-dependent.
 */
class MainMetricNamesTest {

  private static Set<String> metricNamesFor(String... args) {
    Main plugin = new Main(args);

    plugin.afterOperationSetUp("dummy", 0, false);
    plugin.beforeOperationTearDown("dummy", 0, 1_000_000L);

    Map<String, Long> results = new LinkedHashMap<>();
    plugin.onMeasurementResultsRequested(
      "dummy", 0, (benchmark, metric, value) -> results.put(metric, value)
    );
    return results.keySet();
  }

  private static boolean anyNameStartsWith(Set<String> names, String prefix) {
    return names.stream().anyMatch(name -> name.startsWith(prefix));
  }

  private static boolean anyNameEndsWith(Set<String> names, String suffix) {
    return names.stream().anyMatch(name -> name.endsWith(suffix));
  }

  @Test
  void withNoArgumentsReportsNothingAtAll() {
    // Every metric is opt-in: no arguments means no metrics.
    assertEquals(Set.of(), metricNamesFor());
  }

  @Test
  void gcCountReportsOnlyRawUnmappedCollectorNames() {
    Set<String> names = metricNamesFor("gc:count");

    assertFalse(names.contains("jmx_mem_young_collection_count"));
    assertTrue(anyNameStartsWith(names, "jmx_gc_"));
  }

  @Test
  void memUsedReportsExactlyThatOneMetric() {
    assertEquals(Set.of("jmx_mem_heap_used_bytes"), metricNamesFor("mem:used"));
  }

  @Test
  void mempoolAllReportsAtLeastOneHeapAndOneNonHeapPool() {
    Set<String> names = metricNamesFor("mempool:all");

    assertTrue(anyNameStartsWith(names, "jmx_mempool_heap_"));
    assertTrue(anyNameStartsWith(names, "jmx_mempool_nonheap_"));
  }

  @Test
  void threadNotGivenReportsNoAllocationMetric() {
    assertFalse(metricNamesFor("mem:used").contains("jmx_thread_total_allocated_bytes"));
  }

  @Test
  void jitTimeReportsExactlyThatOneMetric() {
    assertEquals(Set.of("jmx_jit_total_compilation_time_ms"), metricNamesFor("jit:time"));
  }

  @Test
  void jitAllReportsBaseOnly() {
    // Delta is a separate, explicit annotation -- 'all' alone selects base values only.
    assertEquals(Set.of("jmx_jit_total_compilation_time_ms"), metricNamesFor("jit:all"));
  }

  @Test
  void jitAllAtBothReportsBaseAndDelta() {
    assertEquals(
      Set.of("jmx_jit_total_compilation_time_ms", "jmx_jit_total_compilation_time_ms_delta"),
      metricNamesFor("jit:all@both")
    );
  }

  @Test
  void jitAllAtDeltaReportsDeltaOnly() {
    assertEquals(
      Set.of("jmx_jit_total_compilation_time_ms_delta"),
      metricNamesFor("jit:all@delta")
    );
  }

  @Test
  void mempoolPeakAtDeltaReportsOnlyDeltaMetric() {
    Set<String> names = metricNamesFor("mempool:peak@delta,nonheap-peak@delta");

    assertTrue(anyNameEndsWith(names, "_peak_bytes_delta"));
    assertFalse(anyNameEndsWith(names, "_peak_bytes"));
  }

  @Test
  void osSystemLoadDeltaIsIndependentOfLoadAverage() {
    assumeTrue(
      ManagementFactory.getOperatingSystemMXBean()
        instanceof com.sun.management.OperatingSystemMXBean
    );

    Set<String> names = metricNamesFor("os:system-load@both,load-average");

    assertTrue(names.contains("jmx_os_system_cpu_load_mpct"));
    assertTrue(names.contains("jmx_os_system_cpu_load_mpct_delta"));
    assertTrue(names.contains("jmx_os_system_load_average_x100"));
    assertFalse(names.contains("jmx_os_system_load_average_x100_delta"));
  }

  @Test
  void legacyMemoryReportsExactLegacyNames() {
    assertEquals(
      Set.of(
        "jmx_memory_young_collection_count", "jmx_memory_young_collection_delta",
        "jmx_memory_young_collection_total_ms", "jmx_memory_young_collection_time_ms",
        "jmx_memory_old_collection_count", "jmx_memory_old_collection_delta",
        "jmx_memory_old_collection_total_ms", "jmx_memory_old_collection_time_ms",
        "jmx_memory_used_size", "jmx_memory_used_delta"
      ),
      metricNamesFor("legacy:memory")
    );
  }

  @Test
  void legacyTimersReportsExactLegacyNames() {
    assertEquals(
      Set.of("jmx_timers_compilation_total_ms", "jmx_timers_compilation_time_ms"),
      metricNamesFor("legacy:timers")
    );
  }

  @Test
  void legacyNotGivenReportsNoLegacyMetrics() {
    Set<String> names = metricNamesFor("mem:used");

    assertFalse(anyNameStartsWith(names, "jmx_memory_"));
    assertFalse(anyNameStartsWith(names, "jmx_timers_"));
  }

  @Test
  void threadCountsReportExactlyThoseFourMetrics() {
    assertEquals(
      Set.of(
        "jmx_thread_count", "jmx_thread_daemon_count",
        "jmx_thread_peak_count", "jmx_thread_started_count"
      ),
      metricNamesFor("thread:count,daemon-count,peak-count,started-count")
    );
  }

  @Test
  void threadCurrentTimeReportsCpuAndUserTime() {
    assumeTrue(ManagementFactory.getThreadMXBean().isCurrentThreadCpuTimeSupported());

    assertEquals(
      Set.of("jmx_thread_current_cpu_time_ns", "jmx_thread_current_user_time_ns"),
      metricNamesFor("thread:cpu-time,user-time")
    );
  }

  @Test
  void threadAllocNotGivenReportsNoAllocationMetric() {
    assertFalse(metricNamesFor("thread:count").contains("jmx_thread_total_allocated_bytes"));
  }

  @Test
  void runtimeAllReportsStartTimeAndUptimeBaseOnly() {
    assertEquals(
      Set.of("jmx_runtime_vm_start_time_ms", "jmx_runtime_vm_uptime_ms"),
      metricNamesFor("runtime:all")
    );
  }

  @Test
  void runtimeUptimeAtBothReportsBaseAndDelta() {
    assertEquals(
      Set.of("jmx_runtime_vm_uptime_ms", "jmx_runtime_vm_uptime_ms_delta"),
      metricNamesFor("runtime:vm-uptime@both")
    );
  }

  @Test
  void classAllReportsExactlyThoseThreeMetrics() {
    assertEquals(
      Set.of("jmx_class_live_count", "jmx_class_total_loaded_count", "jmx_class_total_unloaded_count"),
      metricNamesFor("class:all")
    );
  }

  @Test
  void classLiveCountAtDeltaReportsDeltaOnly() {
    assertEquals(
      Set.of("jmx_class_live_count_delta"),
      metricNamesFor("class:live-count@delta")
    );
  }
}
