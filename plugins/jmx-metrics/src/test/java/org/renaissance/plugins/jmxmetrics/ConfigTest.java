package org.renaissance.plugins.jmxmetrics;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.EnumSource;

import org.renaissance.plugins.jmxmetrics.Config.Key;
import org.renaissance.plugins.jmxmetrics.Config.Token;

import java.util.EnumSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

class ConfigTest {

  /** Asserts {@code expected} is exactly the set of tokens selected in base form. */
  private static void assertSelected(Selection selection, EnumSet<Token> expected) {
    for (Token token : Token.values()) {
      assertEquals(expected.contains(token), selection.contains(token), token.toString());
    }
  }

  /** Asserts {@code expected} is exactly the set of tokens carrying {@code annotation}. */
  private static void assertSelected(Selection selection, Token annotation, EnumSet<Token> expected) {
    for (Token token : Token.values()) {
      assertEquals(expected.contains(token), selection.contains(token, annotation), token.toString());
    }
  }

  @ParameterizedTest
  @EnumSource(Key.class)
  void withNoArgumentsNoKeyIsGiven(Key key) {
    Config config = Config.parse(new String[0]);

    assertFalse(config.isGiven(key), key + " should not be given");
  }

  @Test
  void mempoolAllExpandsToMetricTokensButNotResetPeaks() {
    // Unannotated 'all' selects only metric tokens. It must not imply
    // the 'reset-peaks' behavior toggle or the 'delta' annotation.
    Config config = Config.parse(new String[] { "mempool:all" });
    Selection selection = config.selectionFor(Key.MEMPOOL);

    assertSelected(
      selection, EnumSet.of(
        Token.USED, Token.NONHEAP_USED, Token.PEAK, Token.NONHEAP_PEAK
      )
    );
    assertSelected(selection, Token.DELTA, Tokens.emptySet());
    assertFalse(selection.contains(Token.RESET_PEAKS));
  }

  @Test
  void mempoolAllWithResetPeaksEnablesResetPeaks() {
    Config config = Config.parse(new String[] { "mempool:all,reset-peaks" });
    Selection selection = config.selectionFor(Key.MEMPOOL);

    assertTrue(selection.contains(Token.RESET_PEAKS));
    assertTrue(selection.contains(Token.USED));
  }

  @Test
  void resetPeaksAloneNeedsNoMetricToken() {
    Config config = Config.parse(new String[] { "mempool:reset-peaks" });

    assertTrue(config.isGiven(Key.MEMPOOL));
    Selection selection = config.selectionFor(Key.MEMPOOL);
    assertTrue(selection.contains(Token.RESET_PEAKS));
    assertSelected(selection, EnumSet.of(Token.RESET_PEAKS));
    assertSelected(selection, Token.DELTA, Tokens.emptySet());
  }

  @Test
  void keysAndTokensAreCaseInsensitive() {
    Config config = Config.parse(new String[] { "MEMPOOL:USED,PEAK" });

    assertTrue(config.isGiven(Key.MEMPOOL));
    Selection selection = config.selectionFor(Key.MEMPOOL);
    assertSelected(selection, EnumSet.of(Token.USED, Token.PEAK));
  }

  @Test
  void unrecognizedTokenIsDroppedButOthersAreKept() {
    Config config = Config.parse(new String[] { "mempool:xyz,used" });
    Selection selection = config.selectionFor(Key.MEMPOOL);

    assertSelected(selection, EnumSet.of(Token.USED));
  }

  @Test
  void tokenValidForAnotherKeyIsDroppedForThisOne() {
    // 'count' is a real token (valid for gc:), but not valid for mempool:.
    Config config = Config.parse(new String[] { "mempool:count,used" });
    Selection selection = config.selectionFor(Key.MEMPOOL);

    assertSelected(selection, EnumSet.of(Token.USED));
  }

  @ParameterizedTest
  @EnumSource(Key.class)
  void unrecognizedKeyDoesNotThrowAndGivesNothing(Key key) {
    Config config = Config.parse(new String[] { "bogus:x,y" });

    assertFalse(config.isGiven(key));
  }

  @Test
  void nonAsciiWhitespaceOnlyEntryIsSilentlyIgnored() {
    // Unicode non-breaking space is blank according to Character.isSpaceChar()
    // and should be stripped and filtered out silently by rawEntriesFrom().
    Config config = Config.parse(new String[] { "gc:count,\u00A0,time" });
    Selection selection = config.selectionFor(Key.GC);

    assertSelected(selection, EnumSet.of(Token.COUNT, Token.TIME));
  }

  @Test
  void plainDeltaIsRejectedWithWarningAndDropped() {
    // A plain 'delta' token is invalid, it must annotate a token via '@'.
    Config config = Config.parse(new String[] { "gc:count,time,delta" });
    Selection selection = config.selectionFor(Key.GC);

    assertSelected(selection, EnumSet.of(Token.COUNT, Token.TIME));
    assertSelected(selection, Token.DELTA, Tokens.emptySet());
  }

  @Test
  void tokenAtBothAddsBaseAndDeltaForThatTokenOnly() {
    Config config = Config.parse(new String[] { "gc:count@both,time" });
    Selection selection = config.selectionFor(Key.GC);

    assertSelected(selection, EnumSet.of(Token.COUNT, Token.TIME));
    assertSelected(selection, Token.DELTA, EnumSet.of(Token.COUNT));
  }

  @Test
  void tokenAtDeltaGivesDeltaOnlyForThatToken() {
    Config config = Config.parse(new String[] { "gc:count@delta,time" });
    Selection selection = config.selectionFor(Key.GC);

    assertSelected(selection, EnumSet.of(Token.TIME));
    assertSelected(selection, Token.DELTA, EnumSet.of(Token.COUNT));
  }

  @Test
  void sameTokenPlainAndAtDeltaBothPresentKeepsBase() {
    // '@delta' on one entry never removes a token that another
    // entry in the same argument already put in the base set.
    Config config = Config.parse(new String[] { "gc:count,count@delta" });
    Selection selection = config.selectionFor(Key.GC);

    assertSelected(selection, EnumSet.of(Token.COUNT));
    assertSelected(selection, Token.DELTA, EnumSet.of(Token.COUNT));
  }

  @Test
  void tokenAtBaseIsImmuneToADeltaWildcard() {
    Config config = Config.parse(new String[] { "gc:count@base,time,@delta" });
    Selection selection = config.selectionFor(Key.GC);

    assertSelected(selection, EnumSet.of(Token.COUNT));
    assertSelected(selection, Token.DELTA, EnumSet.of(Token.TIME));
  }

  @Test
  void allAtBaseBlocksALaterWildcardForTheWholeKey() {
    Config config = Config.parse(new String[] { "gc:all@base,@delta" });
    Selection selection = config.selectionFor(Key.GC);

    assertSelected(selection, EnumSet.of(Token.COUNT, Token.TIME));
    assertSelected(selection, Token.DELTA, Tokens.emptySet());
  }

  @Test
  void wildcardBothAddsDeltaToEverythingSelected() {
    Config config = Config.parse(new String[] { "gc:count,time,@both" });
    Selection selection = config.selectionFor(Key.GC);

    assertSelected(selection, EnumSet.of(Token.COUNT, Token.TIME));
    assertSelected(selection, Token.DELTA, EnumSet.of(Token.COUNT, Token.TIME));
  }

  @Test
  void wildcardDeltaClearsBaseSet() {
    Config config = Config.parse(new String[] { "gc:count,time,@delta" });
    Selection selection = config.selectionFor(Key.GC);

    assertSelected(selection, Tokens.emptySet());
    assertSelected(selection, Token.DELTA, EnumSet.of(Token.COUNT, Token.TIME));
  }

  @Test
  void wildcardDeltaDoesNotClearBehaviorTokens() {
    Config config = Config.parse(new String[] { "mempool:used,reset-peaks,@delta" });
    Selection selection = config.selectionFor(Key.MEMPOOL);

    assertSelected(selection, EnumSet.of(Token.RESET_PEAKS));
    assertSelected(selection, Token.DELTA, EnumSet.of(Token.USED));
    assertTrue(selection.contains(Token.RESET_PEAKS));
  }

  @Test
  void wildcardDeltaDoesNotOverrideExplicitlyAnnotatedToken() {
    // A wildcard '@delta' only fills in a default for tokens without
    // their own annotation. It never overrides what an explicit
    // annotation ('count@both') already established for that token.
    Config config = Config.parse(new String[] { "gc:count@both,time,@delta" });
    Selection selection = config.selectionFor(Key.GC);

    assertSelected(selection, EnumSet.of(Token.COUNT));
    assertSelected(selection, Token.DELTA, EnumSet.of(Token.COUNT, Token.TIME));
  }

  @Test
  void conflictingWildcardsLastOneWins() {
    Config config = Config.parse(new String[] { "os:load-average,@both,@delta" });
    Selection selection = config.selectionFor(Key.OS);

    assertSelected(selection, Tokens.emptySet());
    assertSelected(selection, Token.DELTA, EnumSet.of(Token.LOAD_AVERAGE));
  }

  @Test
  void conflictingWildcardsLastOneWinsTheOtherWay() {
    Config config = Config.parse(new String[] { "os:load-average,@delta,@both" });
    Selection selection = config.selectionFor(Key.OS);

    assertSelected(selection, EnumSet.of(Token.LOAD_AVERAGE));
    assertSelected(selection, Token.DELTA, EnumSet.of(Token.LOAD_AVERAGE));
  }

  @Test
  void behaviorTokenCannotBeAnnotated() {
    Config config = Config.parse(new String[] { "mempool:used,reset-peaks@both" });
    Selection selection = config.selectionFor(Key.MEMPOOL);

    assertSelected(selection, EnumSet.of(Token.USED));
    assertFalse(selection.contains(Token.RESET_PEAKS));
    assertSelected(selection, Token.DELTA, Tokens.emptySet());
  }

  @Test
  void osTokensAreIndependentlyAnnotatable() {
    Config config = Config.parse(new String[] { "os:system-load@both,load-average" });
    Selection selection = config.selectionFor(Key.OS);

    assertSelected(selection, EnumSet.of(Token.SYSTEM_LOAD, Token.LOAD_AVERAGE));
    assertSelected(selection, Token.DELTA, EnumSet.of(Token.SYSTEM_LOAD));
  }

  @Test
  void unknownAnnotationIsRejected() {
    Config config = Config.parse(new String[] { "gc:count@bogus" });
    Selection selection = config.selectionFor(Key.GC);

    assertSelected(selection, Tokens.emptySet());
    assertSelected(selection, Token.DELTA, Tokens.emptySet());
  }

  @Test
  void malformedEntryWithTwoAtSignsIsRejected() {
    Config config = Config.parse(new String[] { "gc:time@delta@both" });
    Selection selection = config.selectionFor(Key.GC);

    assertSelected(selection, Tokens.emptySet());
    assertSelected(selection, Token.DELTA, Tokens.emptySet());
  }

  @Test
  void emptyAnnotationIsRejected() {
    Config config = Config.parse(new String[] { "gc:time@,count" });
    Selection selection = config.selectionFor(Key.GC);

    assertSelected(selection, EnumSet.of(Token.COUNT));
    assertSelected(selection, Token.DELTA, Tokens.emptySet());
  }

  @Test
  void jitAllExpandsToTimeOnly() {
    Config config = Config.parse(new String[] { "jit:all" });
    Selection selection = config.selectionFor(Key.JIT);

    assertSelected(selection, EnumSet.of(Token.TIME));
    assertSelected(selection, Token.DELTA, Tokens.emptySet());
  }

  @Test
  void jitAllAtBothGivesBaseAndDelta() {
    Config config = Config.parse(new String[] { "jit:all@both" });
    Selection selection = config.selectionFor(Key.JIT);

    assertSelected(selection, EnumSet.of(Token.TIME));
    assertSelected(selection, Token.DELTA, EnumSet.of(Token.TIME));
  }

  @Test
  void jitAllAtDeltaGivesDeltaOnly() {
    Config config = Config.parse(new String[] { "jit:all@delta" });
    Selection selection = config.selectionFor(Key.JIT);

    assertSelected(selection, Tokens.emptySet());
    assertSelected(selection, Token.DELTA, EnumSet.of(Token.TIME));
  }

  @Test
  void legacyMemoryAndTimersAreIndependentlySelectable() {
    Config config = Config.parse(new String[] { "legacy:memory" });
    Selection selection = config.selectionFor(Key.LEGACY);

    assertTrue(selection.contains(Token.MEMORY));
    assertFalse(selection.contains(Token.TIMERS));
  }

  @Test
  void legacyAllSelectsBothMemoryAndTimers() {
    Config config = Config.parse(new String[] { "legacy:all" });
    Selection selection = config.selectionFor(Key.LEGACY);

    assertTrue(selection.contains(Token.MEMORY));
    assertTrue(selection.contains(Token.TIMERS));
  }

  @Test
  void legacyRejectsAnnotation() {
    // The 'legacy' key supports no annotations. An invalid annotation
    // drops the whole entry, same as an unknown annotation text would.
    Config config = Config.parse(new String[] { "legacy:memory@both" });
    Selection selection = config.selectionFor(Key.LEGACY);

    assertFalse(selection.contains(Token.MEMORY));
  }

  @Test
  void threadAllExpandsToEveryThreadMetricTokenButNotResetPeaks() {
    Config config = Config.parse(new String[] { "thread:all" });
    Selection selection = config.selectionFor(Key.THREAD);

    assertSelected(
      selection, EnumSet.of(
        Token.ALLOC, Token.CPU_TIME, Token.USER_TIME,
        Token.COUNT, Token.DAEMON_COUNT, Token.PEAK_COUNT, Token.STARTED_COUNT
      )
    );
    assertFalse(selection.contains(Token.RESET_PEAKS));
  }

  @Test
  void threadResetPeaksAloneNeedsNoMetricToken() {
    Config config = Config.parse(new String[] { "thread:reset-peaks" });

    assertTrue(config.isGiven(Key.THREAD));
    Selection selection = config.selectionFor(Key.THREAD);
    assertTrue(selection.contains(Token.RESET_PEAKS));
    assertSelected(selection, EnumSet.of(Token.RESET_PEAKS));
  }

  @Test
  void threadPeakCountWithResetPeaksEnablesResetPeaks() {
    Config config = Config.parse(new String[] { "thread:peak-count,reset-peaks" });
    Selection selection = config.selectionFor(Key.THREAD);

    assertTrue(selection.contains(Token.RESET_PEAKS));
    assertTrue(selection.contains(Token.PEAK_COUNT));
  }

  @Test
  void runtimeTokensAreIndependentlyAnnotatable() {
    Config config = Config.parse(new String[] { "runtime:vm-uptime@both,vm-start-time" });
    Selection selection = config.selectionFor(Key.RUNTIME);

    assertSelected(selection, EnumSet.of(Token.VM_UPTIME, Token.VM_START_TIME));
    assertSelected(selection, Token.DELTA, EnumSet.of(Token.VM_UPTIME));
  }

  @Test
  void runtimeAllSelectsBothStartTimeAndUptime() {
    Config config = Config.parse(new String[] { "runtime:all" });
    Selection selection = config.selectionFor(Key.RUNTIME);

    assertSelected(selection, EnumSet.of(Token.VM_START_TIME, Token.VM_UPTIME));
  }

  @Test
  void classAllSelectsAllThreeCounts() {
    Config config = Config.parse(new String[] { "class:all" });
    Selection selection = config.selectionFor(Key.CLASS);

    assertSelected(
      selection, EnumSet.of(Token.LIVE_COUNT, Token.TOTAL_LOADED_COUNT, Token.TOTAL_UNLOADED_COUNT)
    );
  }

  @Test
  void classTokensAreIndependentlyAnnotatable() {
    Config config = Config.parse(new String[] { "class:live-count@both,total-unloaded-count" });
    Selection selection = config.selectionFor(Key.CLASS);

    assertSelected(selection, EnumSet.of(Token.LIVE_COUNT, Token.TOTAL_UNLOADED_COUNT));
    assertSelected(selection, Token.DELTA, EnumSet.of(Token.LIVE_COUNT));
  }
}
