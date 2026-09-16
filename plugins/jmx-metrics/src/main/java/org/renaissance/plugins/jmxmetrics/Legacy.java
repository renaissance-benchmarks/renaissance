package org.renaissance.plugins.jmxmetrics;

import java.lang.management.CompilationMXBean;
import java.lang.management.GarbageCollectorMXBean;
import java.lang.management.ManagementFactory;
import java.lang.management.MemoryMXBean;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.function.LongSupplier;
import java.util.function.ToLongFunction;

import org.renaissance.plugins.jmxmetrics.Config.Token;

import static java.util.Collections.emptyList;
import static org.renaissance.plugins.jmxmetrics.MetricSet.warn;

/**
 * Provides metric values with names that reproduce the 'jmx-memory' and
 * 'jmx-timers' plugins. While the plugin is not a drop-in replacement, it
 * can be used without changing the downstream data processing pipeline.
 */
final class Legacy {
  private Legacy() {}

  private static final Set<String> YOUNG_GC_NAMES =
    Set.of("G1 Young Generation", "PS Scavenge", "Copy");
  private static final Set<String> OLD_GC_NAMES =
    Set.of("G1 Old Generation", "PS MarkSweep", "MarkSweepCompact");

  /** The metrics selected by 'legacy:memory' and/or 'legacy:timers'. */
  static List<Metric> create(Selection selection) {
    List<Metric> result = new ArrayList<>();

    if (selection.contains(Token.MEMORY)) {
      result.addAll(createMemoryMetrics());
    }

    if (selection.contains(Token.TIMERS)) {
      result.addAll(createTimersMetrics());
    }

    return result;
  }

  static List<Metric> createMemoryMetrics() {
    List<GarbageCollectorMXBean> gcBeans = ManagementFactory.getGarbageCollectorMXBeans();
    Optional<GarbageCollectorMXBean> young = findGcBean("young", YOUNG_GC_NAMES, gcBeans);
    Optional<GarbageCollectorMXBean> old = findGcBean("old", OLD_GC_NAMES, gcBeans);
    MemoryMXBean memoryBean = ManagementFactory.getMemoryMXBean();

    return Metric.listOf(
      Metric.optionally(
        "jmx_memory_young_collection_count", true,
        "jmx_memory_young_collection_delta", true,
        gcSupplier(young, GarbageCollectorMXBean::getCollectionCount)
      ),
      Metric.optionally(
        "jmx_memory_young_collection_total_ms", true,
        "jmx_memory_young_collection_time_ms", true,
        gcSupplier(young, GarbageCollectorMXBean::getCollectionTime)
      ),
      Metric.optionally(
        "jmx_memory_old_collection_count", true,
        "jmx_memory_old_collection_delta", true,
        gcSupplier(old, GarbageCollectorMXBean::getCollectionCount)
      ),
      Metric.optionally(
        "jmx_memory_old_collection_total_ms", true,
        "jmx_memory_old_collection_time_ms", true,
        gcSupplier(old, GarbageCollectorMXBean::getCollectionTime)
      ),
      Metric.optionally(
        "jmx_memory_used_size", true,
        "jmx_memory_used_delta", true,
        () -> Metric.usedOf(memoryBean.getHeapMemoryUsage())
      )
    );
  }

  /** Finds the GC bean jmx-memory identified by generation name among {@code beans}. Warns once if none matches. */
  static Optional<GarbageCollectorMXBean> findGcBean(
    String generation, Set<String> names, List<GarbageCollectorMXBean> beans
  ) {
    Optional<GarbageCollectorMXBean> bean = beans.stream()
      .filter(candidate -> names.contains(candidate.getName()))
      .findFirst();

    if (bean.isEmpty()) {
      warn("legacy:memory: no GC bean matches the %s generation (reporting -1).", generation);
    }

    return bean;
  }

  static LongSupplier gcSupplier(
    Optional<GarbageCollectorMXBean> bean, ToLongFunction<GarbageCollectorMXBean> reader
  ) {
    return bean.<LongSupplier>map(b -> () -> reader.applyAsLong(b)).orElse(() -> -1L);
  }

  static List<Metric> createTimersMetrics() {
    return createTimersMetrics(ManagementFactory.getCompilationMXBean());
  }

  static List<Metric> createTimersMetrics(CompilationMXBean bean) {
    if (bean == null) {
      warn("legacy:timers: this JVM does not have a compilation system.");
      return emptyList();
    }

    return Metric.listOf(
      Metric.optionally(
        "jmx_timers_compilation_total_ms", true,
        "jmx_timers_compilation_time_ms", true,
        bean::getTotalCompilationTime
      )
    );
  }
}
