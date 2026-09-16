package org.renaissance.plugins.jmxmetrics;

import java.lang.management.OperatingSystemMXBean;
import java.util.List;
import java.util.stream.Stream;

import org.renaissance.plugins.jmxmetrics.Config.Token;

import static java.util.Collections.emptyList;
import static java.util.stream.Collectors.toList;
import static org.renaissance.plugins.jmxmetrics.MetricSet.warn;

/**
 * Operating system metrics from {@link OperatingSystemMXBean} and
 * {@code com.sun.management.OperatingSystemMXBean} (where available).
 * Load average and available-processor count come from the portable
 * interface, while process CPU time and system/process CPU load rely
 * on the platform-specific interface and are omitted (with a warning)
 * if the extended interface is not available.
 */
final class OperatingSystemMetrics {
  private final OperatingSystemMXBean bean; // nullable: can happen on some JVMs in containers

  OperatingSystemMetrics(OperatingSystemMXBean bean) {
    this.bean = bean;
  }

  List<Metric> create(Selection selection, String prefix) {
    if (bean == null) {
      warn("This JVM does not provide an operating system management bean.");
      return emptyList();
    }

    Stream<Metric> portable = Metric.streamOf(
      Metric.optionallyWithDelta(
        prefix + "system_load_average_x100",
        selection.contains(Token.LOAD_AVERAGE),
        selection.contains(Token.LOAD_AVERAGE, Token.DELTA),
        () -> percentScaled(bean.getSystemLoadAverage())
      ),
      Metric.optionallyWithDelta(
        prefix + "available_processors_count",
        selection.contains(Token.PROCESSORS),
        selection.contains(Token.PROCESSORS, Token.DELTA),
        () -> (long) bean.getAvailableProcessors()
      )
    );

    Stream<Metric> platformSpecific;
    if (bean instanceof com.sun.management.OperatingSystemMXBean) {
      com.sun.management.OperatingSystemMXBean extBean =
        (com.sun.management.OperatingSystemMXBean) bean;

      platformSpecific = Metric.streamOf(
        Metric.optionallyWithDelta(
          prefix + "system_cpu_load_mpct",
          selection.contains(Token.SYSTEM_LOAD),
          selection.contains(Token.SYSTEM_LOAD, Token.DELTA),
          () -> asMilliPercent(extBean.getSystemCpuLoad())
        ),
        Metric.optionallyWithDelta(
          prefix + "process_cpu_load_mpct",
          selection.contains(Token.PROCESS_LOAD),
          selection.contains(Token.PROCESS_LOAD, Token.DELTA),
          () -> asMilliPercent(extBean.getProcessCpuLoad())
        ),
        Metric.optionallyWithDelta(
          prefix + "process_cpu_time_ns",
          selection.contains(Token.PROCESS_TIME),
          selection.contains(Token.PROCESS_TIME, Token.DELTA),
          extBean::getProcessCpuTime
        )
      );
    } else {
      boolean includeExtended = selection.containsAnyOf(
        Token.SYSTEM_LOAD, Token.PROCESS_TIME, Token.PROCESS_LOAD
      );

      if (includeExtended) {
        warn("This JVM does not provide extended OperatingSystemMXBean interface.");
      }

      platformSpecific = Stream.empty();
    }

    return Stream.concat(portable, platformSpecific).collect(toList());
  }

  /**
   * Scales an absolute value (e.g. load average) by 100 for 2-decimal
   * fixed-point representation, preserving a negative sentinel (per the
   * underlying MXBean methods, meaning "not available") as -1 rather than
   * a scaled negative number.
   */
  private static long percentScaled(double value) {
    return value < 0 ? -1L : Math.round(value * 100);
  }

  /**
   * Scales a 0..1 fraction into milli-percent integer, preserving -1 as
   * a negative sentinel (meaning "not available") used by MXBeans.
   */
  private static long asMilliPercent(double value) {
    return value < 0 ? -1L : Math.round(value * 100_000);
  }
}
