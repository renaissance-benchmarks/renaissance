package org.renaissance.plugins.jmxmetrics;

import org.junit.jupiter.api.Test;

import javax.management.ObjectName;
import java.lang.management.MemoryPoolMXBean;
import java.lang.management.MemoryType;
import java.lang.management.MemoryUsage;
import java.util.List;

import org.renaissance.plugins.jmxmetrics.Config.Key;

import static org.junit.jupiter.api.Assertions.assertArrayEquals;
import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Covers a case that {@link MainMetricNamesTest} cannot distinguish from the
 * outside: whether 'reset-peaks' resets a pool that was only selected for
 * its used-bytes metric and that should not be reset.
 */
class MemoryPoolMetricsTest {

  private static MemoryPoolMXBean fakePool(String name, MemoryType type) {
    MemoryUsage usage = new MemoryUsage(0, 1, 2, 3);
    return new MemoryPoolMXBean() {
      @Override public String getName() { return name; }
      @Override public MemoryType getType() { return type; }
      @Override public MemoryUsage getUsage() { return usage; }
      @Override public MemoryUsage getPeakUsage() { return usage; }
      @Override public void resetPeakUsage() { }
      @Override public boolean isValid() { return true; }
      @Override public String[] getMemoryManagerNames() { return new String[0]; }
      @Override public long getUsageThreshold() { return 0; }
      @Override public void setUsageThreshold(long threshold) { }
      @Override public boolean isUsageThresholdExceeded() { return false; }
      @Override public long getUsageThresholdCount() { return 0; }
      @Override public boolean isUsageThresholdSupported() { return false; }
      @Override public long getCollectionUsageThreshold() { return 0; }
      @Override public void setCollectionUsageThreshold(long threshold) { }
      @Override public boolean isCollectionUsageThresholdExceeded() { return false; }
      @Override public long getCollectionUsageThresholdCount() { return 0; }
      @Override public boolean isCollectionUsageThresholdSupported() { return false; }
      @Override public MemoryUsage getCollectionUsage() { return usage; }
      @Override public ObjectName getObjectName() { return null; }
    };
  }

  @Test
  void poolSelectedOnlyForUsedIsNotResetEvenWithResetPeaks() {
    MemoryPoolMXBean pool = fakePool("Eden", MemoryType.HEAP);
    MemoryPoolMXBean[] resettablePools = new MemoryPoolMetrics(List.of(pool))
      .resettableBeans(Selection.parse(Key.MEMPOOL, "used,reset-peaks"));

    assertArrayEquals(new MemoryPoolMXBean[0], resettablePools);
  }

  @Test
  void poolSelectedForPeakIsResetWithResetPeaks() {
    MemoryPoolMXBean pool = fakePool("Eden", MemoryType.HEAP);
    MemoryPoolMXBean[] resettablePools = new MemoryPoolMetrics(List.of(pool))
      .resettableBeans(Selection.parse(Key.MEMPOOL, "peak,reset-peaks"));

    assertArrayEquals(new MemoryPoolMXBean[] { pool }, resettablePools);
  }

  @Test
  void poolSelectedForBothIsResetOnlyWhenResetPeaksIsGiven() {
    MemoryPoolMXBean pool = fakePool("Eden", MemoryType.HEAP);
    MemoryPoolMXBean[] resettablePools = new MemoryPoolMetrics(List.of(pool))
      .resettableBeans(Selection.parse(Key.MEMPOOL, "used,peak"));

    assertArrayEquals(new MemoryPoolMXBean[0], resettablePools);
  }

  @Test
  void nonheapPoolTracksNonheapPeakTokenNotHeapPeakToken() {
    MemoryPoolMXBean pool = fakePool("Metaspace", MemoryType.NON_HEAP);
    MemoryPoolMXBean[] resettablePools = new MemoryPoolMetrics(List.of(pool))
      .resettableBeans(Selection.parse(Key.MEMPOOL, "peak,reset-peaks"));

    // 'peak' (the heap token) was selected, not 'nonheap-peak', so the
    // peak of this non-heap pool itself was never actually requested.
    assertArrayEquals(new MemoryPoolMXBean[0], resettablePools);
  }

  @Test
  void peakDeltaOnlyStillCountsAsTrackingThePeak() {
    MemoryPoolMXBean pool = fakePool("Eden", MemoryType.HEAP);
    MemoryPoolMXBean[] resettablePools = new MemoryPoolMetrics(List.of(pool))
      .resettableBeans(Selection.parse(Key.MEMPOOL, "peak@delta,reset-peaks"));

    assertArrayEquals(new MemoryPoolMXBean[] { pool }, resettablePools);
  }
}
