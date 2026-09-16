package org.renaissance.plugins.jmxmetrics;

import org.junit.jupiter.api.Test;

import java.lang.management.ManagementFactory;
import java.lang.management.ThreadInfo;
import java.lang.management.ThreadMXBean;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import org.renaissance.plugins.jmxmetrics.Config.Key;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Covers the paths that {@link MainMetricNamesTest} cannot reach portably:
 * current-thread CPU/user time unsupported, and (via the platform-specific
 * interface) thread allocation tracking unavailable in either of its two
 * ways. Both depend on what the real JVM happens to support, so they are
 * tested against fakes instead. The reflection-resolved happy path for
 * {@code getTotalThreadAllocatedBytes()} is left to the real-bean coverage
 * in {@link MainMetricNamesTest}, because faking a JDK-21-only default method
 * given the current Java 11 compile target is not practical.
 */
class ThreadMetricsTest {

  /** A plain, portable-only bean -- deliberately not the extended interface. */
  private static class FakeThreadBean implements ThreadMXBean {
    int threadCount = 24;
    int daemonThreadCount = 18;
    int peakThreadCount = 27;
    long totalStartedThreadCount = 142;
    boolean currentThreadCpuTimeSupported = true;
    boolean threadCpuTimeEnabled = false;
    long currentThreadCpuTime = 48_123_456L;
    long currentThreadUserTime = 41_120_000L;
    boolean resetPeakCalled = false;

    @Override public int getThreadCount() { return threadCount; }
    @Override public int getPeakThreadCount() { return peakThreadCount; }
    @Override public long getTotalStartedThreadCount() { return totalStartedThreadCount; }
    @Override public int getDaemonThreadCount() { return daemonThreadCount; }
    @Override public long[] getAllThreadIds() { return new long[0]; }
    @Override public ThreadInfo getThreadInfo(long id) { return null; }
    @Override public ThreadInfo[] getThreadInfo(long[] ids) { return new ThreadInfo[0]; }
    @Override public ThreadInfo getThreadInfo(long id, int maxDepth) { return null; }
    @Override public ThreadInfo[] getThreadInfo(long[] ids, int maxDepth) { return new ThreadInfo[0]; }
    @Override public boolean isThreadContentionMonitoringSupported() { return false; }
    @Override public boolean isThreadContentionMonitoringEnabled() { return false; }
    @Override public void setThreadContentionMonitoringEnabled(boolean enable) { }
    @Override public long getCurrentThreadCpuTime() { return currentThreadCpuTime; }
    @Override public long getCurrentThreadUserTime() { return currentThreadUserTime; }
    @Override public long getThreadCpuTime(long id) { return 0; }
    @Override public long getThreadUserTime(long id) { return 0; }
    @Override public boolean isThreadCpuTimeSupported() { return currentThreadCpuTimeSupported; }
    @Override public boolean isCurrentThreadCpuTimeSupported() { return currentThreadCpuTimeSupported; }
    @Override public boolean isThreadCpuTimeEnabled() { return threadCpuTimeEnabled; }
    @Override public void setThreadCpuTimeEnabled(boolean enable) { threadCpuTimeEnabled = enable; }
    @Override public long[] findMonitorDeadlockedThreads() { return null; }
    @Override public void resetPeakThreadCount() { resetPeakCalled = true; }
    @Override public long[] findDeadlockedThreads() { return null; }
    @Override public boolean isObjectMonitorUsageSupported() { return false; }
    @Override public boolean isSynchronizerUsageSupported() { return false; }
    @Override public ThreadInfo[] getThreadInfo(long[] ids, boolean lockedMonitors, boolean lockedSynchronizers) {
      return new ThreadInfo[0];
    }
    @Override public ThreadInfo[] dumpAllThreads(boolean lockedMonitors, boolean lockedSynchronizers) {
      return new ThreadInfo[0];
    }
    @Override public javax.management.ObjectName getObjectName() { return null; }
  }

  /** Extends the portable fake with the platform-specific allocation-tracking interface. */
  private static class FakeExtendedThreadBean extends FakeThreadBean
      implements com.sun.management.ThreadMXBean {
    boolean threadAllocatedMemorySupported = true;
    boolean threadAllocatedMemoryEnabled = false;

    @Override public long[] getThreadCpuTime(long[] ids) { return new long[0]; }
    @Override public long[] getThreadUserTime(long[] ids) { return new long[0]; }
    @Override public boolean isThreadAllocatedMemorySupported() { return threadAllocatedMemorySupported; }
    @Override public boolean isThreadAllocatedMemoryEnabled() { return threadAllocatedMemoryEnabled; }
    @Override public void setThreadAllocatedMemoryEnabled(boolean enable) { threadAllocatedMemoryEnabled = enable; }
    @Override public long getThreadAllocatedBytes(long id) { return 0; }
    @Override public long[] getThreadAllocatedBytes(long[] ids) { return new long[0]; }
  }

  private static Set<String> namesOf(List<Metric> metrics) {
    return metrics.stream().map(m -> m.baseName).collect(Collectors.toSet());
  }

  @Test
  void countsAreIndependentlySelectable() {
    FakeThreadBean bean = new FakeThreadBean();
    List<Metric> metrics = new ThreadMetrics(bean)
      .create(Selection.parse(Key.THREAD, "count,peak-count"), "jmx_thread_");

    assertEquals(Set.of("jmx_thread_count", "jmx_thread_peak_count"), namesOf(metrics));
  }

  @Test
  void currentThreadTimeUnsupportedReportsNothing() {
    FakeThreadBean bean = new FakeThreadBean();
    bean.currentThreadCpuTimeSupported = false;

    List<Metric> metrics = new ThreadMetrics(bean)
      .create(Selection.parse(Key.THREAD, "cpu-time,user-time"), "jmx_thread_");

    assertTrue(metrics.isEmpty());
  }

  @Test
  void currentThreadTimeGetsEnabledWhenNotAlready() {
    FakeThreadBean bean = new FakeThreadBean();
    assertFalse(bean.threadCpuTimeEnabled);

    new ThreadMetrics(bean).create(Selection.parse(Key.THREAD, "cpu-time"), "jmx_thread_");

    assertTrue(bean.threadCpuTimeEnabled);
  }

  @Test
  void currentThreadTimeAlreadyEnabledIsLeftAlone() {
    FakeThreadBean bean = new FakeThreadBean();
    bean.threadCpuTimeEnabled = true;

    new ThreadMetrics(bean).create(Selection.parse(Key.THREAD, "cpu-time"), "jmx_thread_");

    assertTrue(bean.threadCpuTimeEnabled);
  }

  @Test
  void notSelectedNeverChecksCurrentThreadTimeSupport() {
    // A bean that would throw if asked is never asked, because nothing selected it.
    ThreadMXBean bean = new FakeThreadBean() {
      @Override public boolean isCurrentThreadCpuTimeSupported() {
        throw new AssertionError("should not be called: cpu-time/user-time not selected");
      }
    };

    List<Metric> metrics = new ThreadMetrics(bean)
      .create(Selection.parse(Key.THREAD, "count"), "jmx_thread_");

    assertEquals(Set.of("jmx_thread_count"), namesOf(metrics));
  }

  @Test
  void allocNotExtendedInterfaceReportsNothing() {
    FakeThreadBean bean = new FakeThreadBean(); // plain interface, not the extended one

    List<Metric> metrics = new ThreadMetrics(bean)
      .create(Selection.parse(Key.THREAD, "alloc"), "jmx_thread_");

    assertTrue(metrics.isEmpty());
  }

  @Test
  void allocUnsupportedOnExtendedInterfaceReportsNothing() {
    FakeExtendedThreadBean bean = new FakeExtendedThreadBean();
    bean.threadAllocatedMemorySupported = false;

    List<Metric> metrics = new ThreadMetrics(bean)
      .create(Selection.parse(Key.THREAD, "alloc"), "jmx_thread_");

    assertTrue(metrics.isEmpty());
  }

  @Test
  void resettableBeanIsNullWithoutResetPeaks() {
    ThreadMXBean resettableBean = new ThreadMetrics(new FakeThreadBean())
      .resettableBean(Selection.parse(Key.THREAD, "peak-count"));

    assertEquals(null, resettableBean);
  }

  @Test
  void resettableBeanIsSetWithResetPeaks() {
    FakeThreadBean bean = new FakeThreadBean();
    ThreadMXBean resettableBean = new ThreadMetrics(bean)
      .resettableBean(Selection.parse(Key.THREAD, "peak-count,reset-peaks"));

    assertEquals(bean, resettableBean);
    assertFalse(bean.resetPeakCalled); // resettableBean() only wires it up; resetting happens per-operation.
  }

  @Test
  void resetPeaksWithoutPeakCountLeavesNothingToReset() {
    // Nothing reads peak-count here, so resetting it every operation would
    // be pure overhead with no observable effect.
    ThreadMXBean resettableBean = new ThreadMetrics(new FakeThreadBean())
      .resettableBean(Selection.parse(Key.THREAD, "count,reset-peaks"));

    assertEquals(null, resettableBean);
  }

  @Test
  void realBeanIsStillUsableEndToEnd() {
    // Sanity check that the real ThreadMXBean of the JDK satisfies everything
    // ThreadMetrics needs, independent of the fakes above.
    List<Metric> metrics = new ThreadMetrics(ManagementFactory.getThreadMXBean())
      .create(Selection.parse(Key.THREAD, "all"), "jmx_thread_");

    assertTrue(namesOf(metrics).contains("jmx_thread_count"));
  }
}
