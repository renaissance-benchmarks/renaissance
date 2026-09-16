package org.renaissance.plugins.jmxmetrics;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.EnumSource;

import org.renaissance.plugins.jmxmetrics.Config.Key;
import org.renaissance.plugins.jmxmetrics.Config.Token;

import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

class KeyTest {

  @ParameterizedTest
  @EnumSource(Key.class)
  void fromTextRoundTripsForEveryKey(Key key) {
    assertEquals(Optional.of(key), Key.fromText(key.text));
  }

  @Test
  void fromTextRejectsUnknownKey() {
    assertEquals(Optional.empty(), Key.fromText("bogus"));
  }

  @ParameterizedTest
  @EnumSource(Key.class)
  void resetPeaksIsAcceptedOnlyByKeysWithAPeakToReset(Key key) {
    boolean hasAPeak = key == Key.MEMPOOL || key == Key.THREAD;
    assertEquals(
      hasAPeak, key.accepts(Token.RESET_PEAKS),
      "whether " + key + " accepts 'reset-peaks'"
    );
  }

  @ParameterizedTest
  @EnumSource(Key.class)
  void everyKeyKnowsAllButDoesNotSelectItAsAMetric(Key key) {
    assertTrue(key.accepts(Token.ALL), key + " should accept 'all'");
    assertFalse(
      key.acceptsMetric(Token.ALL),
      key + "'s metricTokens should not include ALL itself"
    );
  }

  @ParameterizedTest
  @EnumSource(value = Key.class, names = "LEGACY", mode = EnumSource.Mode.EXCLUDE)
  void baseDeltaAndBothAreAnnotationTokensNotMetricOrBehaviorTokens(Key key) {
    for (Token annotation : new Token[] { Token.BASE, Token.DELTA, Token.BOTH }) {
      assertTrue(key.acceptsAnnotation(annotation), key + " should annotate with '" + annotation.text + "'");
      assertTrue(key.accepts(annotation), key + " should accept '" + annotation.text + "'");
      assertFalse(
        key.acceptsMetric(annotation),
        "metricTokens of " + key + " should not include " + annotation
      );
      assertFalse(
        key.acceptsBehavior(annotation),
        "behaviorTokens of " + key + " should not include " + annotation
      );
    }
  }

  @Test
  void legacySupportsNoAnnotationAtAll() {
    for (Token annotation : new Token[] { Token.BASE, Token.DELTA, Token.BOTH }) {
      assertFalse(Key.LEGACY.acceptsAnnotation(annotation));
      assertFalse(Key.LEGACY.accepts(annotation));
    }
  }
}
