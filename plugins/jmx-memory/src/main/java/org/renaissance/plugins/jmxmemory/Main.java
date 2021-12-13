package org.renaissance.plugins.jmxmemory;

import java.lang.management.GarbageCollectorMXBean;
import java.lang.management.ManagementFactory;
import java.lang.management.MemoryMXBean;
import java.lang.management.MemoryUsage;
import javax.management.ObjectName;

import org.renaissance.Plugin;

public class Main implements Plugin,
    Plugin.AfterOperationSetUpListener,
    Plugin.BeforeOperationTearDownListener,
    Plugin.MeasurementResultPublisher {

  /** Mock garbage collector MX bean.
   *
   * Returns values that should be easy to distinguish from true MX beans
   * and are marking the data as invalid.
   * Methods that are not even called are implemented as least-effort.
   */
  private static class MockGCBean implements GarbageCollectorMXBean {
    @Override
    public long getCollectionCount() {
      return -1;
    }

    @Override
    public long getCollectionTime() {
      return -1;
    }

    @Override
    public String[] getMemoryPoolNames() {
      return new String[] { "this-is-mock" };
    }

    @Override
    public boolean isValid() {
      return false;
    }

    @Override
    public String getName() {
      return this.getClass().getName();
    }

    @Override
    public ObjectName getObjectName() {
      return null;
    }
  }


  GarbageCollectorMXBean youngGenerationMXBean;
  GarbageCollectorMXBean oldGenerationMXBean;
  MemoryMXBean memoryMXBean;

  long youngCollectionsBefore;
  long youngCollectionsAfter;
  long youngTimeBefore;
  long youngTimeAfter;

  long oldCollectionsBefore;
  long oldCollectionsAfter;
  long oldTimeBefore;
  long oldTimeAfter;

  MemoryUsage memoryUsageBefore;
  MemoryUsage memoryUsageAfter;

  public Main() {
    for (GarbageCollectorMXBean collector : ManagementFactory.getGarbageCollectorMXBeans()) {
      String name = collector.getName();
      if (name.equals("G1 Young Generation")) {
        youngGenerationMXBean = collector;
      } else if (name.equals("G1 Old Generation")) {
        oldGenerationMXBean = collector;
      } else if (name.equals("PS Scavenge")) {
        youngGenerationMXBean = collector;
      } else if (name.equals("PS MarkSweep")) {
        oldGenerationMXBean = collector;
      } else {
        warn("Unknown garbage collector %s.", name);
      }
    }

    if (youngGenerationMXBean == null) {
      warn("MXBean for young generation not found, using mock.");
      youngGenerationMXBean = new MockGCBean();
    }
    if (oldGenerationMXBean == null) {
      warn("MXBean for old generation not found, using mock.");
      oldGenerationMXBean = new MockGCBean();
    }

    memoryMXBean = ManagementFactory.getMemoryMXBean();
  }

  @Override
  public void afterOperationSetUp(String benchmark, int opIndex, boolean isLastOp) {
    youngCollectionsBefore = youngGenerationMXBean.getCollectionCount();
    oldCollectionsBefore = oldGenerationMXBean.getCollectionCount();
    youngTimeBefore = youngGenerationMXBean.getCollectionTime();
    oldTimeBefore = oldGenerationMXBean.getCollectionTime();
    memoryUsageBefore = memoryMXBean.getHeapMemoryUsage();
  }

  @Override
  public void beforeOperationTearDown(String benchmark, int opIndex, long harnessDuration) {
    youngCollectionsAfter = youngGenerationMXBean.getCollectionCount();
    oldCollectionsAfter = oldGenerationMXBean.getCollectionCount();
    youngTimeAfter = youngGenerationMXBean.getCollectionTime();
    oldTimeAfter = oldGenerationMXBean.getCollectionTime();
    memoryUsageAfter = memoryMXBean.getHeapMemoryUsage();
  }

  @Override
  public void onMeasurementResultsRequested(String benchmark, int opIndex, Plugin.MeasurementResultListener dispatcher) {
    dispatcher.onMeasurementResult(benchmark, "jmx_memory_young_collection_count", youngCollectionsAfter);
    dispatcher.onMeasurementResult(benchmark, "jmx_memory_young_collection_delta", youngCollectionsAfter - youngCollectionsBefore);
    dispatcher.onMeasurementResult(benchmark, "jmx_memory_young_collection_total_ms", youngTimeAfter);
    dispatcher.onMeasurementResult(benchmark, "jmx_memory_young_collection_time_ms", youngTimeAfter - youngTimeBefore);
    dispatcher.onMeasurementResult(benchmark, "jmx_memory_old_collection_count", oldCollectionsAfter);
    dispatcher.onMeasurementResult(benchmark, "jmx_memory_old_collection_delta", oldCollectionsAfter - oldCollectionsBefore);
    dispatcher.onMeasurementResult(benchmark, "jmx_memory_old_collection_total_ms", oldTimeAfter);
    dispatcher.onMeasurementResult(benchmark, "jmx_memory_old_collection_time_ms", oldTimeAfter - oldTimeBefore);
    dispatcher.onMeasurementResult(benchmark, "jmx_memory_used_size", memoryUsageAfter.getUsed());
    dispatcher.onMeasurementResult(benchmark, "jmx_memory_used_delta", memoryUsageAfter.getUsed() - memoryUsageBefore.getUsed());
  }

  private void warn(String msg, Object... args) {
    System.err.printf("[jmx-memory plugin] WARNING: " + msg + "\n", args);
  }
}
