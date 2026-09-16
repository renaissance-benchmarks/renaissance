package org.renaissance.plugins.jmxmetrics;

import org.renaissance.plugins.jmxmetrics.Config.Key;

import java.lang.management.ManagementFactory;
import java.lang.management.MemoryPoolMXBean;
import java.lang.management.ThreadMXBean;
import java.util.ArrayList;
import java.util.List;

/**
 * Looks up the JMX bean each metric family needs and requests {@link Metric}
 * instances for the selection in {@link Config}, each with an output prefix
 * reflecting the key. Exposes plain fields (the selected metrics, split into
 * the ones with a base value and the ones with a delta, plus the beans whose
 * peaks need resetting) for a harness-specific glue class to use directly.
 */
final class MetricSet {
  final Metric[] metrics;
  final Metric[] baseMetrics;
  final Metric[] deltaMetrics;
  final MemoryPoolMXBean[] resettableMemoryPoolBeans;
  final ThreadMXBean resettableThreadBean;

  MetricSet(
    Metric[] metrics, Metric[] baseMetrics, Metric[] deltaMetrics,
    MemoryPoolMXBean[] resettableMemoryPoolBeans, ThreadMXBean resettableThreadBean
  ) {
    this.metrics = metrics;
    this.baseMetrics = baseMetrics;
    this.deltaMetrics = deltaMetrics;
    this.resettableMemoryPoolBeans = resettableMemoryPoolBeans;
    this.resettableThreadBean = resettableThreadBean;
  }

  static void warn(String msg, Object... args) {
    System.err.printf("[jmx-metrics plugin] WARNING: " + msg + "\n", args);
  }

  public static MetricSet from(Config config) {
    final List<Metric> localMetrics = new ArrayList<>();

    localMetrics.addAll(
      new MemoryMetrics(ManagementFactory.getMemoryMXBean())
        .create(config.selectionFor(Key.MEM), "jmx_mem_")
    );
    localMetrics.addAll(
      new GarbageCollectorMetrics(ManagementFactory.getGarbageCollectorMXBeans())
        .create(config.selectionFor(Key.GC), "jmx_gc_")
    );
    localMetrics.addAll(
      new CompilationMetrics(ManagementFactory.getCompilationMXBean())
        .create(config.selectionFor(Key.JIT), "jmx_jit_")
    );
    localMetrics.addAll(
      new OperatingSystemMetrics(ManagementFactory.getOperatingSystemMXBean())
        .create(config.selectionFor(Key.OS), "jmx_os_")
    );
    localMetrics.addAll(
      new RuntimeMetrics(ManagementFactory.getRuntimeMXBean())
        .create(config.selectionFor(Key.RUNTIME), "jmx_runtime_")
    );
    localMetrics.addAll(
      new ClassLoadingMetrics(ManagementFactory.getClassLoadingMXBean())
        .create(config.selectionFor(Key.CLASS), "jmx_class_")
    );

    localMetrics.addAll(Legacy.create(config.selectionFor(Key.LEGACY)));

    Selection mempoolSelection = config.selectionFor(Key.MEMPOOL);
    MemoryPoolMetrics poolMetrics = new MemoryPoolMetrics(ManagementFactory.getMemoryPoolMXBeans());
    localMetrics.addAll(poolMetrics.create(mempoolSelection, "jmx_mempool_"));

    Selection threadSelection = config.selectionFor(Key.THREAD);
    ThreadMetrics threadMetrics = new ThreadMetrics(ManagementFactory.getThreadMXBean());
    localMetrics.addAll(threadMetrics.create(threadSelection, "jmx_thread_"));

    return new MetricSet(
      localMetrics.toArray(Metric[]::new),
      localMetrics.stream().filter(Metric::hasBase).toArray(Metric[]::new),
      localMetrics.stream().filter(Metric::hasDelta).toArray(Metric[]::new),
      poolMetrics.resettableBeans(mempoolSelection),
      threadMetrics.resettableBean(threadSelection)
    );
  }

}
