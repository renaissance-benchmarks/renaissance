package org.renaissance.plugins.jmxmetrics;

import org.junit.jupiter.api.Test;

import javax.management.ObjectName;
import java.lang.management.CompilationMXBean;
import java.lang.management.GarbageCollectorMXBean;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.function.LongSupplier;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Covers the two paths the end-to-end checks in {@link MainMetricNamesTest}
 * cannot reach portably: no GC bean matching a generation, and no compilation
 * system at all. Both depend on the beans happened to be provided by the real
 * JVM, so they are tested against fakes instead.
 */
class LegacyTest {

  private static GarbageCollectorMXBean fakeGcBean(String name, long count, long time) {
    return new GarbageCollectorMXBean() {
      @Override public long getCollectionCount() { return count; }
      @Override public long getCollectionTime() { return time; }
      @Override public String getName() { return name; }
      @Override public boolean isValid() { return true; }
      @Override public String[] getMemoryPoolNames() { return new String[0]; }
      @Override public ObjectName getObjectName() { return null; }
    };
  }

  private static CompilationMXBean fakeCompilationBean(long totalTime) {
    return new CompilationMXBean() {
      @Override public String getName() { return "fake"; }
      @Override public boolean isCompilationTimeMonitoringSupported() { return true; }
      @Override public long getTotalCompilationTime() { return totalTime; }
      @Override public ObjectName getObjectName() { return null; }
    };
  }

  @Test
  void findGcBeanReturnsTheMatchingBean() {
    GarbageCollectorMXBean match = fakeGcBean("PS Scavenge", 1, 2);
    List<GarbageCollectorMXBean> beans = List.of(fakeGcBean("Unrelated", 9, 9), match);

    assertEquals(Optional.of(match), Legacy.findGcBean("young", Set.of("PS Scavenge"), beans));
  }

  @Test
  void findGcBeanReturnsEmptyWhenNoBeanMatches() {
    List<GarbageCollectorMXBean> beans = List.of(fakeGcBean("Unrelated", 9, 9));

    assertTrue(Legacy.findGcBean("young", Set.of("PS Scavenge"), beans).isEmpty());
  }

  @Test
  void gcSupplierReadsFromThePresentBean() {
    LongSupplier supplier = Legacy.gcSupplier(
      Optional.of(fakeGcBean("PS Scavenge", 42, 7)), GarbageCollectorMXBean::getCollectionCount
    );

    assertEquals(42L, supplier.getAsLong());
  }

  @Test
  void gcSupplierFallsBackToNegativeOneWhenBeanMissing() {
    LongSupplier supplier = Legacy.gcSupplier(Optional.empty(), GarbageCollectorMXBean::getCollectionCount);

    assertEquals(-1L, supplier.getAsLong());
  }

  @Test
  void createTimersMetricsIsEmptyWithoutACompilationSystem() {
    assertTrue(Legacy.createTimersMetrics(null).isEmpty());
  }

  @Test
  void createTimersMetricsReportsBothNamesWithACompilationSystem() {
    List<Metric> metrics = Legacy.createTimersMetrics(fakeCompilationBean(123));

    assertEquals(1, metrics.size());
    assertEquals("jmx_timers_compilation_total_ms", metrics.get(0).baseName);
    assertEquals("jmx_timers_compilation_time_ms", metrics.get(0).deltaName);
  }
}
