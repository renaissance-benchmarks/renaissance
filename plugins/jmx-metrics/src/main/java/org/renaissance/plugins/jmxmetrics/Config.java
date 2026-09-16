package org.renaissance.plugins.jmxmetrics;

import java.util.Arrays;
import java.util.EnumMap;
import java.util.EnumSet;
import java.util.Locale;
import java.util.Map;
import java.util.Optional;

import static java.util.stream.Collectors.toMap;
import static org.renaissance.plugins.jmxmetrics.MetricSet.warn;

/**
 * Parsed plugin arguments, keyed by {@link Key}. Every key is associated
 * with a set of tokens in different roles that select which metrics to
 * report and how, and possibly enable other actions. Nothing is reported
 * if nothing is selected. Delegates the actual parsing of the value of each
 * key to {@link Selection}; handles the given/not-given bookkeeping and decides
 * when an empty result is worth a warning.
 */
final class Config {
  /**
   * Vocabulary of all tokens recognized across all argument keys. The meaning
   * of a token is derived from the key/context that checks for it (e.g.
   * {@code USED} may mean different things under {@code mem:} and under
   * {@code mempool:}).
   */
  enum Token {
    USED("used"),
    NONHEAP_USED("nonheap-used"),
    BASE("base"),
    DELTA("delta"),
    BOTH("both"),
    PEAK("peak"),
    NONHEAP_PEAK("nonheap-peak"),
    COUNT("count"),
    TIME("time"),
    ALLOC("alloc"),
    CPU_TIME("cpu-time"),
    USER_TIME("user-time"),
    DAEMON_COUNT("daemon-count"),
    PEAK_COUNT("peak-count"),
    STARTED_COUNT("started-count"),
    VM_START_TIME("vm-start-time"),
    VM_UPTIME("vm-uptime"),
    LIVE_COUNT("live-count"),
    TOTAL_LOADED_COUNT("total-loaded-count"),
    TOTAL_UNLOADED_COUNT("total-unloaded-count"),
    LOAD_AVERAGE("load-average"),
    PROCESSORS("processors"),
    PROCESS_TIME("process-time"),
    SYSTEM_LOAD("system-load"),
    PROCESS_LOAD("process-load"),
    RESET_PEAKS("reset-peaks"),
    MEMORY("memory"),
    TIMERS("timers"),
    ALL("all");

    private static final Map<String, Token> BY_TEXT = Arrays.stream(values())
      .collect(toMap(token -> token.text, token -> token));

    final String text;

    Token(String text) {
      this.text = text;
    }

    static Optional<Token> fromText(String text) {
      return Optional.ofNullable(BY_TEXT.get(text));
    }
  }

  /**
   * A plugin argument key (e.g., 'mem:') with tokens recognized
   * in different roles:<ul>
   * <li>{@code metricTokens}, what a plain token selects and what
   * {@link Token#ALL 'all'} expands to, can be annotated,
   * <li>{@code behaviorTokens}, plain only, independent of
   * {@link Token#ALL 'all'}, never annotatable (e.g., 'reset-peaks'), and
   * <li>{@code annotationTokens}, valid only as the right-hand side of a
   * {@code token@ann} pair, or as a plain wildcard {@code @ann} ('base',
   * 'delta', or 'both', where supported).
   * </ul>
   * {@code knownTokens} is the union of all three, plus {@code ALL}.
   */
  enum Key {
    MEM("mem", EnumSet.of(Token.USED, Token.NONHEAP_USED)),

    MEMPOOL(
      "mempool",
      EnumSet.of(Token.USED, Token.NONHEAP_USED, Token.PEAK, Token.NONHEAP_PEAK),
      EnumSet.of(Token.RESET_PEAKS)
    ),

    GC("gc", EnumSet.of(Token.COUNT, Token.TIME)),

    THREAD(
      "thread",
      EnumSet.of(
        Token.ALLOC, Token.CPU_TIME, Token.USER_TIME,
        Token.COUNT, Token.DAEMON_COUNT, Token.PEAK_COUNT, Token.STARTED_COUNT
      ),
      EnumSet.of(Token.RESET_PEAKS)
    ),

    JIT("jit", EnumSet.of(Token.TIME)),

    OS("os", EnumSet.of(
      Token.LOAD_AVERAGE, Token.PROCESSORS, Token.PROCESS_TIME,
      Token.SYSTEM_LOAD, Token.PROCESS_LOAD
    )),

    RUNTIME("runtime", EnumSet.of(Token.VM_START_TIME, Token.VM_UPTIME)),

    CLASS("class", EnumSet.of(Token.LIVE_COUNT, Token.TOTAL_LOADED_COUNT, Token.TOTAL_UNLOADED_COUNT)),

    /**
     * Reproduces metrics from the 'jmx-memory' and 'jmx-timers' plugins.
     * Does not support any annotations or behavior tokens.
     */
    LEGACY(
      "legacy", EnumSet.of(Token.MEMORY, Token.TIMERS),
      Tokens.emptySet(), Tokens.emptySet()
    );

    private static final Map<String, Key> keysByText = Arrays.stream(values())
      .collect(toMap(key -> key.text, key -> key));

    final String text;
    final EnumSet<Token> metricTokens;
    final EnumSet<Token> behaviorTokens;
    final EnumSet<Token> annotationTokens;
    final EnumSet<Token> knownTokens;

    Key(String text, EnumSet<Token> metricTokens) {
      this(text, metricTokens, Tokens.emptySet());
    }

    Key(String text, EnumSet<Token> metricTokens, EnumSet<Token> behaviorTokens) {
      this(text, metricTokens, behaviorTokens, EnumSet.of(Token.BASE, Token.DELTA, Token.BOTH));
    }

    Key(
      String text, EnumSet<Token> metricTokens,
      EnumSet<Token> behaviorTokens, EnumSet<Token> annotationTokens
    ) {
      this.text = text;
      this.metricTokens = metricTokens;
      this.behaviorTokens = behaviorTokens;
      this.annotationTokens = annotationTokens;

      this.knownTokens = Tokens.emptySet();
      this.knownTokens.addAll(metricTokens);
      this.knownTokens.addAll(behaviorTokens);
      this.knownTokens.addAll(annotationTokens);
      this.knownTokens.add(Token.ALL);
    }

    static Optional<Key> fromText(String text) {
      return Optional.ofNullable(keysByText.get(text));
    }

    boolean acceptsMetric(Token token) {
      return metricTokens.contains(token);
    }

    boolean acceptsBehavior(Token token) {
      return behaviorTokens.contains(token);
    }

    boolean acceptsAnnotation(Token token) {
      return annotationTokens.contains(token);
    }

    boolean accepts(Token token) {
      return knownTokens.contains(token);
    }

    boolean acceptsAll(EnumSet<Token> tokens) {
      return knownTokens.containsAll(tokens);
    }

    /** A fresh, independently mutable copy of every metric token of this key. */
    EnumSet<Token> allMetricTokens() {
      return EnumSet.copyOf(metricTokens);
    }

    /** The subset of {@code tokens} that are metric tokens of this key. */
    EnumSet<Token> metricTokensAmong(EnumSet<Token> tokens) {
      EnumSet<Token> result = EnumSet.copyOf(tokens);
      result.retainAll(metricTokens);
      return result;
    }
  }

  private final Map<Key, Selection> selectionsByKey;

  private Config(Map<Key, Selection> selectionsByKey) {
    this.selectionsByKey = selectionsByKey;
  }

  static Config parse(String[] args) {
    Map<Key, Selection> selectionsByKey = new EnumMap<>(Key.class);

    for (String rawArg : args) {
      String arg = rawArg.toLowerCase(Locale.ROOT);

      int sep = arg.indexOf(':');
      String keyText = ((sep < 0) ? arg : arg.substring(0, sep)).strip();
      String value = (sep < 0) ? "" : arg.substring(sep + 1);

      Optional<Key> key = Key.fromText(keyText);
      if (key.isEmpty()) {
        warn("ignoring argument '%s' with unknown key '%s'.", rawArg, keyText);
        continue;
      }

      Selection selection = Selection.parse(key.get(), value);
      if (!selection.selectsAnyMetric()) {
        warn("the '%s' argument key selected no metrics.", keyText);
        // Keep the empty selection (may contain non-metric tokens).
      }

      selectionsByKey.put(key.get(), selection);
    }

    return new Config(selectionsByKey);
  }

  boolean isGiven(Key key) {
    return selectionsByKey.containsKey(key);
  }

  /** The token selection for this key. Empty (selects nothing) if the key was never given. */
  Selection selectionFor(Key key) {
    return selectionsByKey.getOrDefault(key, Selection.empty(key));
  }
}
