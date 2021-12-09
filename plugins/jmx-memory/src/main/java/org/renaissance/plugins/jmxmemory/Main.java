package org.renaissance.plugins.jmxmemory;

import java.lang.management.GarbageCollectorMXBean;
import java.lang.management.ManagementFactory;
import java.lang.management.MemoryMXBean;
import java.lang.management.MemoryUsage;

import org.renaissance.Plugin;

public class Main implements Plugin,
    Plugin.AfterOperationSetUpListener,
    Plugin.BeforeOperationTearDownListener,
    Plugin.MeasurementResultPublisher {

  GarbageCollectorMXBean __youngGenerationMXBean;
  GarbageCollectorMXBean __oldGenerationMXBean;
  MemoryMXBean __memoryMXBean;

  long __youngCollectionsBefore;
  long __youngCollectionsAfter;
  long __youngTimeBefore;
  long __youngTimeAfter;

  long __oldCollectionsBefore;
  long __oldCollectionsAfter;
  long __oldTimeBefore;
  long __oldTimeAfter;

  MemoryUsage __memoryUsageBefore;
  MemoryUsage __memoryUsageAfter;

  public Main() {
    for (GarbageCollectorMXBean collector : ManagementFactory.getGarbageCollectorMXBeans ()) {
      String name = collector.getName ();
           if (name.equals ("G1 Young Generation")) __youngGenerationMXBean = collector;
      else if (name.equals ("G1 Old Generation")) __oldGenerationMXBean = collector;
      else if (name.equals ("PS Scavenge")) __youngGenerationMXBean = collector;
      else if (name.equals ("PS MarkSweep")) __oldGenerationMXBean = collector;
      else assert false : String.format ("[jmx-memory] Unknown garbage collector %s.", name);
    }
    __memoryMXBean = ManagementFactory.getMemoryMXBean ();
  }

  @Override
  public void afterOperationSetUp(String benchmark, int opIndex, boolean isLastOp) {
    __youngCollectionsBefore = __youngGenerationMXBean.getCollectionCount ();
    __oldCollectionsBefore = __oldGenerationMXBean.getCollectionCount ();
    __youngTimeBefore = __youngGenerationMXBean.getCollectionTime ();
    __oldTimeBefore = __oldGenerationMXBean.getCollectionTime ();
    __memoryUsageBefore = __memoryMXBean.getHeapMemoryUsage ();
  }

  @Override
  public void beforeOperationTearDown(String benchmark, int opIndex, long harnessDuration) {
    __youngCollectionsAfter = __youngGenerationMXBean.getCollectionCount ();
    __oldCollectionsAfter = __oldGenerationMXBean.getCollectionCount ();
    __youngTimeAfter = __youngGenerationMXBean.getCollectionTime ();
    __oldTimeAfter = __oldGenerationMXBean.getCollectionTime ();
    __memoryUsageAfter = __memoryMXBean.getHeapMemoryUsage ();
  }

  @Override
  public void onMeasurementResultsRequested(String benchmark, int opIndex, Plugin.MeasurementResultListener dispatcher) {
    dispatcher.onMeasurementResult (benchmark, "jmx_memory_young_collection_count", __youngCollectionsAfter);
    dispatcher.onMeasurementResult (benchmark, "jmx_memory_young_collection_delta", __youngCollectionsAfter - __youngCollectionsBefore);
    dispatcher.onMeasurementResult (benchmark, "jmx_memory_young_collection_total_ms", __youngTimeAfter);
    dispatcher.onMeasurementResult (benchmark, "jmx_memory_young_collection_time_ms", __youngTimeAfter - __youngTimeBefore);
    dispatcher.onMeasurementResult (benchmark, "jmx_memory_old_collection_count", __oldCollectionsAfter);
    dispatcher.onMeasurementResult (benchmark, "jmx_memory_old_collection_delta", __oldCollectionsAfter - __oldCollectionsBefore);
    dispatcher.onMeasurementResult (benchmark, "jmx_memory_old_collection_total_ms", __oldTimeAfter);
    dispatcher.onMeasurementResult (benchmark, "jmx_memory_old_collection_time_ms", __oldTimeAfter - __oldTimeBefore);
    dispatcher.onMeasurementResult (benchmark, "jmx_memory_used_size", __memoryUsageAfter.getUsed ());
    dispatcher.onMeasurementResult (benchmark, "jmx_memory_used_delta", __memoryUsageAfter.getUsed () - __memoryUsageBefore.getUsed ());
  }
}
