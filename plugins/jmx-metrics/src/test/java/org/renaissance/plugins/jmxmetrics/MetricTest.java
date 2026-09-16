package org.renaissance.plugins.jmxmetrics;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Optional;
import java.util.concurrent.atomic.AtomicLong;

import static java.util.stream.Collectors.toList;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

class MetricTest {

  @Test
  void optionallyWithBothFlagsProducesBaseAndDelta() {
    Optional<Metric> metric = Metric.optionally("base", true, "delta", true, () -> 0L);

    assertTrue(metric.isPresent());
    assertTrue(metric.get().hasBase());
    assertTrue(metric.get().hasDelta());
    assertEquals("base", metric.get().baseName);
    assertEquals("delta", metric.get().deltaName);
  }

  @Test
  void optionallyWithOnlyBaseProducesBaseOnly() {
    Optional<Metric> metric = Metric.optionally("base", true, "delta", false, () -> 0L);

    assertTrue(metric.get().hasBase());
    assertFalse(metric.get().hasDelta());
  }

  @Test
  void optionallyWithOnlyDeltaProducesDeltaOnly() {
    Optional<Metric> metric = Metric.optionally("base", false, "delta", true, () -> 0L);

    assertFalse(metric.get().hasBase());
    assertTrue(metric.get().hasDelta());
  }

  @Test
  void optionallyWithNeitherFlagProducesNothing() {
    Optional<Metric> metric = Metric.optionally("base", false, "delta", false, () -> 0L);

    assertTrue(metric.isEmpty());
  }

  @Test
  void sampleBeforeAndAfterComputeTheRightDelta() {
    AtomicLong counter = new AtomicLong(10);
    Metric metric = Metric.optionally("base", true, "delta", true, counter::get).get();

    metric.sampleBefore();
    counter.set(25);
    metric.sampleAfter();

    assertEquals(25L, metric.value());
    assertEquals(15L, metric.delta());
  }

  @Test
  void streamOfFlattensPresentEntriesOnlyInOrder() {
    Optional<Metric> a = Metric.optionally("a", true, null, false, () -> 1L);
    Optional<Metric> b = Optional.empty();
    Optional<Metric> c = Metric.optionally("c", true, null, false, () -> 3L);

    List<Metric> result = Metric.listOf(a, b, c);

    assertEquals(List.of("a", "c"), result.stream().map(m -> m.baseName).collect(toList()));
  }
}
