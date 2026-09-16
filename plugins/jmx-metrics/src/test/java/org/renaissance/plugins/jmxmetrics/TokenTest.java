package org.renaissance.plugins.jmxmetrics;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.ValueSource;

import org.renaissance.plugins.jmxmetrics.Config.Token;

import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

class TokenTest {

  @Test
  void fromTextResolvesKnownToken() {
    assertEquals(Optional.of(Token.USED), Token.fromText("used"));
  }

  @Test
  void fromTextRejectsUnknownToken() {
    assertEquals(Optional.empty(), Token.fromText("bogus"));
  }

  @Test
  void fromTextIsCaseSensitive() {
    // Case-folding is the job of Config; Token.fromText expects already-lowercased input.
    assertEquals(Optional.empty(), Token.fromText("USED"));
  }

  @ParameterizedTest
  @ValueSource(strings = { "used-delta", "count-delta", "time-delta", "alloc-delta" })
  void fromTextRejectsPerMetricDeltaSpellings(String spelling) {
    // Delta is expressed via '@' annotation syntax, not via a distinct
    // token spelling per metric, so these aren't recognized tokens.
    assertTrue(Token.fromText(spelling).isEmpty());
  }
}
