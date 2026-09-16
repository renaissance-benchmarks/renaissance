package org.renaissance.plugins.jmxmetrics;

import java.lang.invoke.MethodHandle;
import java.lang.invoke.MethodHandles;
import java.lang.invoke.MethodType;
import java.lang.management.ThreadMXBean;
import java.util.List;
import java.util.Objects;
import java.util.function.LongSupplier;
import java.util.stream.Stream;

import org.renaissance.plugins.jmxmetrics.Config.Token;

import static java.util.function.Function.identity;
import static java.util.stream.Collectors.toList;
import static org.renaissance.plugins.jmxmetrics.MetricSet.warn;

/**
 * Metrics from {@link ThreadMXBean}: live/peak/daemon/started thread
 * counts, current-thread CPU/user time from the portable interface, and
 * (via the platform-specific interface) total bytes allocated by threads.
 * 'reset-peaks' resets the peak thread count at the start of every
 * operation, so that the peak reflects the high-water mark reached during
 * that operation rather than since JVM start; it has no effect unless
 * peak-count itself was also selected.
 */
final class ThreadMetrics {
  private final ThreadMXBean bean;

  ThreadMetrics(ThreadMXBean bean) {
    this.bean = Objects.requireNonNull(bean);
  }

  List<Metric> create(Selection selection, String prefix) {
    return Stream.of(
        createCountMetrics(selection, prefix),
        createTimeMetrics(selection, prefix),
        createAllocMetrics(selection, prefix)
      )
      .flatMap(identity())
      .collect(toList());
  }

  /**
   * The bean to reset at the start of every operation, or {@code null}
   * unless 'reset-peaks' was given. Resetting the peak thread count is
   * pointless if peak-count itself wasn't selected -- there would be
   * nothing reading the value it resets.
   */
  ThreadMXBean resettableBean(Selection selection) {
    boolean tracksPeak = selection.containsAnyOf(Token.PEAK_COUNT);
    return selection.contains(Token.RESET_PEAKS) && tracksPeak ? bean : null;
  }

  /** Live/peak/daemon/started thread counts. */
  private Stream<Metric> createCountMetrics(Selection selection, String prefix) {
    return Metric.streamOf(
      Metric.optionallyWithDelta(
        prefix + "count",
        selection.contains(Token.COUNT),
        selection.contains(Token.COUNT, Token.DELTA),
        bean::getThreadCount
      ),
      Metric.optionallyWithDelta(
        prefix + "daemon_count",
        selection.contains(Token.DAEMON_COUNT),
        selection.contains(Token.DAEMON_COUNT, Token.DELTA),
        bean::getDaemonThreadCount
      ),
      Metric.optionallyWithDelta(
        prefix + "peak_count",
        selection.contains(Token.PEAK_COUNT),
        selection.contains(Token.PEAK_COUNT, Token.DELTA),
        bean::getPeakThreadCount
      ),
      Metric.optionallyWithDelta(
        prefix + "started_count",
        selection.contains(Token.STARTED_COUNT),
        selection.contains(Token.STARTED_COUNT, Token.DELTA),
        bean::getTotalStartedThreadCount
      )
    );
  }

  /**
   * Current-thread CPU/user time. Note that these provide metrics only for
   * the thread that calls {@link ThreadMXBean#getCurrentThreadCpuTime()}, not
   * for the potentially many threads the benchmark may use.
   */
  private Stream<Metric> createTimeMetrics(Selection selection, String prefix) {
    if (!selection.containsAnyOf(Token.CPU_TIME, Token.USER_TIME)) {
      return Stream.empty();
    }

    if (!bean.isCurrentThreadCpuTimeSupported()) {
      warn("This JVM does not support current-thread CPU/user time measurement.");
      return Stream.empty();
    }

    if (!bean.isThreadCpuTimeEnabled()) {
      // TODO Consider printing a message that this needed enabling.
      bean.setThreadCpuTimeEnabled(true);
    }

    return Metric.streamOf(
      Metric.optionallyWithDelta(
        prefix + "current_cpu_time_ns",
        selection.contains(Token.CPU_TIME),
        selection.contains(Token.CPU_TIME, Token.DELTA),
        bean::getCurrentThreadCpuTime
      ),
      Metric.optionallyWithDelta(
        prefix + "current_user_time_ns",
        selection.contains(Token.USER_TIME),
        selection.contains(Token.USER_TIME, Token.DELTA),
        bean::getCurrentThreadUserTime
      )
    );
  }

  /** Total bytes allocated by threads, from the platform-specific interface. */
  private Stream<Metric> createAllocMetrics(Selection selection, String prefix) {
    if (!selection.containsAnyOf(Token.ALLOC)) {
      return Stream.empty();
    }

    if (!(bean instanceof com.sun.management.ThreadMXBean)) {
      warn("This JVM does not provide extended ThreadMXBean interface.");
      return Stream.empty();
    }

    com.sun.management.ThreadMXBean extBean = (com.sun.management.ThreadMXBean) bean;
    if (!extBean.isThreadAllocatedMemorySupported()) {
      warn("This JVM does not support thread allocated memory measurement.");
      return Stream.empty();
    }

    if (!extBean.isThreadAllocatedMemoryEnabled()) {
      // TODO Consider printing a message that this needed enabling.
      extBean.setThreadAllocatedMemoryEnabled(true);
    }

    LongSupplier totalAllocated = resolveTotalThreadAllocatedBytes(extBean);
    if (totalAllocated == null || totalAllocated.getAsLong() < 0) {
      warn("This JVM does not have a working thread allocated bytes measurement.");
      return Stream.empty();
    }

    return Metric.streamOf(
      Metric.optionallyWithDelta(
        prefix + "total_allocated_bytes",
        selection.contains(Token.ALLOC),
        selection.contains(Token.ALLOC, Token.DELTA),
        totalAllocated
      )
    );
  }

  private static LongSupplier resolveTotalThreadAllocatedBytes(
    com.sun.management.ThreadMXBean bean
  ) {
    try {
      // The lookup (constant class + constant method name) should be safe,
      // because it can be resolved by GraalVM Native Image at build time.
      MethodHandle handle = MethodHandles.publicLookup().findVirtual(
        com.sun.management.ThreadMXBean.class,
        "getTotalThreadAllocatedBytes",
        MethodType.methodType(long.class)
      ).bindTo(bean);

      return () -> {
        try {
          return (long) handle.invokeExact();
        } catch (Throwable t) {
          throw new RuntimeException(t);
        }
      };
    } catch (ReflectiveOperationException e) {
      // Could not resolve the method.
      return null;
    }
  }
}
