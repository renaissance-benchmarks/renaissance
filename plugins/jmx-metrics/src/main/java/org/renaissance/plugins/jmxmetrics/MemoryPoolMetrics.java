package org.renaissance.plugins.jmxmetrics;

import java.lang.management.MemoryPoolMXBean;
import java.lang.management.MemoryType;
import java.util.EnumSet;
import java.util.List;
import java.util.Objects;
import java.util.Set;

import org.renaissance.plugins.jmxmetrics.Config.Token;

import static java.util.stream.Collectors.toList;

/**
 * Memory pool usage metrics from {@link MemoryPoolMXBean}. The
 * {@link Token#RESET_PEAKS reset-peaks} token resets the peak usage of each
 * pool whose peak is being reported, at the start of every operation, so that
 * the peak reflects the high-water mark reached during that operation rather
 * than since JVM start; it has no effect when only the used-bytes metric was
 * selected.
 */
final class MemoryPoolMetrics {
  private final List<MemoryPoolMXBean> beans;

  MemoryPoolMetrics(List<MemoryPoolMXBean> allPools) {
    this.beans = Objects.requireNonNull(allPools);
  }

  List<Metric> create(Selection selection, String prefix) {
    return createMetrics(selection, selectPools(selection), prefix);
  }

  /**
   * The memory pools which needs their peak usage reset at the start of
   * every operation (empty array unless 'reset-peaks' is given and at least
   * one peak-usage metric is selected).
   */
  MemoryPoolMXBean[] resettableBeans(Selection selection) {
    if (!selection.contains(Token.RESET_PEAKS)) {
      return new MemoryPoolMXBean[0];
    }

    return beans.stream()
      .filter(pool -> tracksPeak(selection, pool))
      .toArray(MemoryPoolMXBean[]::new);
  }

  /** Whether the peak of {@code pool} (base or delta, heap or non-heap as applicable) was selected. */
  private static boolean tracksPeak(Selection selection, MemoryPoolMXBean pool) {
    Token peakToken = pool.getType() == MemoryType.HEAP ? Token.PEAK : Token.NONHEAP_PEAK;
    return selection.containsAnyOf(peakToken);
  }

  private List<MemoryPoolMXBean> selectPools(Selection selection) {
    Set<MemoryType> includedTypes = selectTypes(selection);
    return beans.stream().filter(
      pool -> pool.isValid() && includedTypes.contains(pool.getType())
    ).collect(toList());
  }

  private static Set<MemoryType> selectTypes(Selection selection) {
    EnumSet<MemoryType> result = EnumSet.noneOf(MemoryType.class);

    if (selection.containsAnyOf(Token.USED, Token.PEAK)) {
      result.add(MemoryType.HEAP);
    }

    if (selection.containsAnyOf(Token.NONHEAP_USED, Token.NONHEAP_PEAK)) {
      result.add(MemoryType.NON_HEAP);
    }

    return result;
  }

  private static List<Metric> createMetrics(
    Selection selection, List<MemoryPoolMXBean> pools, String prefix
  ) {
    return pools.stream().flatMap(pool -> {
      boolean isHeap = pool.getType() == MemoryType.HEAP;

      String category = isHeap ? "heap" : "nonheap";
      String base = prefix + category + "_" + Metric.sanitize(pool.getName());

      Token usedToken = isHeap ? Token.USED : Token.NONHEAP_USED;
      Token peakToken = isHeap ? Token.PEAK : Token.NONHEAP_PEAK;

      return Metric.streamOf(
        Metric.optionallyWithDelta(
          base + "_used_bytes",
          selection.contains(usedToken),
          selection.contains(usedToken, Token.DELTA),
          () -> Metric.usedOf(pool.getUsage())
        ),
        Metric.optionallyWithDelta(
          base + "_peak_bytes",
          selection.contains(peakToken),
          selection.contains(peakToken, Token.DELTA),
          () -> Metric.usedOf(pool.getPeakUsage())
        )
      );
    }).collect(toList());
  }
}
