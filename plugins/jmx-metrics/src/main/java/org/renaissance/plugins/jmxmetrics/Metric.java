package org.renaissance.plugins.jmxmetrics;

import java.lang.management.MemoryUsage;
import java.util.Arrays;
import java.util.List;
import java.util.Locale;
import java.util.Objects;
import java.util.Optional;
import java.util.function.LongSupplier;
import java.util.stream.Stream;

import static java.util.stream.Collectors.toList;

/**
 * A named counter associated with a provider. Either name may be null
 * (but not both), so that a metric can be reported either as a base
 * value, a delta of "before" and "after" samples, or both.
 */
final class Metric {
  final String baseName;
  final String deltaName;
  final LongSupplier supplier;

  private long before;
  private long after;

  private Metric(String baseName, String deltaName, LongSupplier supplier) {
    this.baseName = baseName;
    this.deltaName = deltaName;
    this.supplier = supplier;
  }

  void sampleBefore() {
    before = supplier.getAsLong();
  }

  void sampleAfter() {
    after = supplier.getAsLong();
  }

  long value() {
    return after;
  }

  long delta() {
    return after - before;
  }

  boolean hasBase() {
    return baseName != null;
  }

  boolean hasDelta() {
    return deltaName != null;
  }

  /**
   * Builds a zero or one {@link Metric} instance reporting
   * one or two values, depending on which representation was
   * requested.
   */
  static Optional<Metric> optionally(
    String baseName, boolean includeBase,
    String deltaName, boolean includeDelta,
    LongSupplier supplier
  ) {
    if (includeBase && includeDelta) {
      // A metric reported both as a base and delta value.
      assert !Objects.requireNonNull(baseName).isBlank();
      assert !Objects.requireNonNull(deltaName).isBlank();
      return Optional.of(new Metric(baseName, deltaName, supplier));
    } else if (includeBase) {
      // A metric reported only as a base (current) value.
      assert !Objects.requireNonNull(baseName).isBlank();
      return Optional.of(new Metric(baseName, null, supplier));
    } else if (includeDelta) {
      // A metric reported only as a delta from the "before" measurement.
      assert !Objects.requireNonNull(deltaName).isBlank();
      return Optional.of(new Metric(null, deltaName, supplier));
    } else {
      return Optional.empty();
    }
  }

  static Optional<Metric> optionallyWithDelta(
    String baseName, boolean includeBase, boolean includeDelta, LongSupplier supplier
  ) {
    return optionally(
      baseName, includeBase,
      includeDelta ? baseName + "_delta" : null, includeDelta,
      supplier
    );
  }

  @SafeVarargs
  static Stream<Metric> streamOf(Optional<Metric> ... metrics) {
    return Arrays.stream(metrics).flatMap(Optional::stream);
  }

  @SafeVarargs
  static List<Metric> listOf(Optional<Metric> ... metrics) {
    return streamOf(metrics).collect(toList());
  }

  /** The used size of a {@link MemoryUsage}, or {@code -1} if unavailable. */
  static long usedOf(MemoryUsage usage) {
    return usage != null ? usage.getUsed() : -1L;
  }

  /** A JVM-supplied name, lower-cased with non-alphanumeric runs collapsed to a single underscore. */
  static String sanitize(String name) {
    return name.toLowerCase(Locale.ROOT).replaceAll("[^a-z0-9]+", "_");
  }
}
