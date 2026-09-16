package org.renaissance.plugins.jmxmetrics;

import java.util.Arrays;
import java.util.Collections;
import java.util.EnumSet;
import java.util.List;
import java.util.Optional;
import java.util.stream.Stream;

import org.renaissance.plugins.jmxmetrics.Config.Key;
import org.renaissance.plugins.jmxmetrics.Config.Token;

import static java.util.stream.Collectors.toList;
import static org.renaissance.plugins.jmxmetrics.MetricSet.warn;

/**
 * Parsed configuration for a {@link Key}: which tokens of the key are
 * selected, and whether each reports its base (current) value, its delta
 * (the change over the measured operation), or both.
 *
 * <p>Each comma-separated entry in the value of a key is a plain token (base
 * only), a {@code token@state} pair ({@code state} one of {@code base},
 * {@code delta}, {@code both}), or a plain {@code @state} wildcard with no
 * token, which fills in {@code state} for every token this key selected
 * that carries no annotation of its own. An explicit annotation on a
 * specific token -- including an explicit {@code @base} -- always stands
 * against any wildcard elsewhere in the same value, regardless of where
 * either appears; a value built from independently authored fragments
 * should not change meaning just because those fragments get concatenated
 * in a different order. With more than one plain wildcard for the same key,
 * the last one given wins.
 */
final class Selection {
  private final Key key;
  private final EnumSet<Token> baseTokens;
  private final EnumSet<Token> deltaTokens;

  private Selection(Key key, EnumSet<Token> baseTokens, EnumSet<Token> deltaTokens) {
    this.key = key;
    this.baseTokens = baseTokens;
    this.deltaTokens = deltaTokens;
  }

  /** A sentinel instance with no selection for a key that was not given. */
  static Selection empty(Key key) {
    return new Selection(key, Tokens.emptySet(), Tokens.emptySet());
  }

  /** Whether the base (current) value of {@code token} should be reported. */
  boolean contains(Token token) {
    assert key.accepts(token) : notATokenOf(token);
    return baseTokens.contains(token);
  }

  /** Whether the delta of {@code token} should be reported. */
  boolean contains(Token token, Token annotation) {
    assert key.accepts(token) : notATokenOf(token);
    assert key.acceptsAnnotation(annotation) : notAnAnnotationOf(annotation);
    return annotation == Token.DELTA && deltaTokens.contains(token);
  }

  /** Whether any of {@code tokens} was selected, in base or delta form. */
  boolean containsAnyOf(Token... tokens) {
    EnumSet<Token> tokenSet = Tokens.emptySet();
    tokenSet.addAll(Arrays.asList(tokens));
    return containsAnyOf(tokenSet);
  }

  private boolean containsAnyOf(EnumSet<Token> tokens) {
    return !Collections.disjoint(baseTokens, tokens) || !Collections.disjoint(deltaTokens, tokens);
  }

  /** Whether this selection selects any of the metric tokens of its key. */
  boolean selectsAnyMetric() {
    return containsAnyOf(key.metricTokens);
  }

  private String notATokenOf(Token token) {
    return "'" + token.text + "' is not a token of '" + key.text + ":...'";
  }

  private String notAnAnnotationOf(Token annotation) {
    return "'" + annotation.text + "' is not a valid annotation for '" + key.text + ":...'";
  }

  /**
   * Converts a value with multiple entries into a {@link Selection}
   * associated with the given {@link Key key}. Each entry is parsed into
   * an {@link Entry}, validated against the vocabulary of {@code key}, and the
   * resulting entries are then folded into a {@link Selection} by
   * {@link #resolve}.
   */
  static Selection parse(Key key, String value) {
    List<Entry> entries = rawEntriesFrom(value)
      .map(raw -> Entry.fromString(raw, key))
      .flatMap(Optional::stream)
      .collect(toList());

    return resolve(key, entries);
  }

  /** Splits a value into trimmed, non-empty, comma-separated entries. */
  private static Stream<String> rawEntriesFrom(String value) {
    return Arrays.stream(value.split(","))
      .map(Selection::stripFully)
      .filter(entry -> !entry.isEmpty());
  }

  /** Strips leading/trailing space characters matching {@link Character#isSpaceChar}. */
  private static String stripFully(String s) {
    int start = 0;
    while (start < s.length() && Character.isSpaceChar(s.charAt(start))) {
      start++;
    }

    int end = s.length();
    while (end > start && Character.isSpaceChar(s.charAt(end - 1))) {
      end--;
    }

    return s.substring(start, end);
  }

  /**
   * Folds parsed entries into base/delta token sets. A plain token, or an
   * explicit {@code @base}/{@code @both}, grants the base value; an
   * explicit {@code @delta}/{@code @both} grants the delta. A plain
   * wildcard then fills in its state for every selected token that
   * carries no explicit annotation of its own.
   */
  private static Selection resolve(Key key, List<Entry> entries) {
    EnumSet<Token> baseTokens = Tokens.emptySet();
    EnumSet<Token> deltaTokens = Tokens.emptySet();
    EnumSet<Token> explicitTokens = Tokens.emptySet();
    Token wildcardState = null;

    for (Entry entry : entries) {
      if (entry.isWildcard()) {
        wildcardState = mergeWildcard(key, wildcardState, entry.wildcardState());
        continue;
      }

      for (Token token : entry.tokens(key)) {
        if (entry.wantsBase()) {
          baseTokens.add(token);
        }
        if (entry.wantsDelta()) {
          deltaTokens.add(token);
        }
        if (entry.isExplicit()) {
          explicitTokens.add(token);
        }
      }
    }

    if (wildcardState != null) {
      EnumSet<Token> unclaimed = unclaimedMetricTokens(key, baseTokens, explicitTokens);
      if (wildcardState == Token.DELTA) {
        baseTokens.removeAll(unclaimed);
      }
      if (wildcardState != Token.BASE) {
        deltaTokens.addAll(unclaimed);
      }
    }

    return new Selection(key, baseTokens, deltaTokens);
  }

  /** With more than one plain wildcard for the same key, the last one given wins. */
  private static Token mergeWildcard(Key key, Token current, Token incoming) {
    if (current != null && current != incoming) {
      warn(
        "both '@%s' and '@%s' given for '%s:...'; using '@%s' (the last one given).",
        current.text, incoming.text, key.text, incoming.text
      );
    }
    return incoming;
  }

  /**
   * The metric tokens of {@code key} that are selected but carry no
   * explicit annotation of their own, and are therefore open to the
   * default of a wildcard. A wildcard never applies to a behavior token like
   * 'reset-peaks', selected or not.
   */
  private static EnumSet<Token> unclaimedMetricTokens(
      Key key, EnumSet<Token> baseTokens, EnumSet<Token> explicitTokens
  ) {
    EnumSet<Token> unclaimed = EnumSet.copyOf(baseTokens);
    unclaimed.retainAll(key.metricTokens);
    unclaimed.removeAll(explicitTokens);
    return unclaimed;
  }

  /**
   * One parsed entry: a plain wildcard if it names no token, otherwise a
   * token (possibly {@link Token#ALL}) with an optional annotation.
   */
  private static final class Entry {
    private final Token token;
    private final Token annotation;

    private Entry(Token token, Token annotation) {
      this.token = token;
      this.annotation = annotation;
    }

    /** Whether this is a plain wildcard: an entry naming no token. */
    boolean isWildcard() {
      return token == null;
    }

    /** The state a plain wildcard fills in. Only meaningful if {@link #isWildcard()}. */
    Token wildcardState() {
      return annotation;
    }

    /** Whether this entry reports the base (current) value. Only meaningful if not {@link #isWildcard()}. */
    boolean wantsBase() {
      return annotation == null || annotation == Token.BASE || annotation == Token.BOTH;
    }

    /** Whether this entry reports the delta. Only meaningful if not {@link #isWildcard()}. */
    boolean wantsDelta() {
      return annotation == Token.DELTA || annotation == Token.BOTH;
    }

    /** Whether this entry carries its own annotation, so that a wildcard for the same key leaves it alone. */
    boolean isExplicit() {
      return annotation != null;
    }

    /** The metric tokens this entry names, expanding {@link Token#ALL} against {@code key}. */
    Iterable<Token> tokens(Key key) {
      return token == Token.ALL ? key.allMetricTokens() : List.of(token);
    }

    /**
     * Parses one comma-separated entry against the vocabulary of {@code key}.
     * An entry naming an unknown token, an annotation that is unknown or
     * not valid here, or carrying more than one {@code '@'}, is dropped
     * whole, with a warning -- a garbled entry that happens to name a
     * real token must not select that token in some unintended form.
     */
    static Optional<Entry> fromString(String raw, Key key) {
      List<String> parts = splitOnAt(raw);
      if (parts.isEmpty()) {
        warn("malformed entry '%s' in '%s:...' (more than one '@').", raw, key.text);
        return Optional.empty();
      }

      String tokenText = parts.get(0).trim();
      String annotationText = parts.size() == 2 ? parts.get(1).trim() : null;

      if (annotationText != null && annotationText.isEmpty()) {
        warn("ignoring entry '%s' in '%s:...' (missing annotation after '@').", raw, key.text);
        return Optional.empty();
      }

      Token token = null;
      if (!tokenText.isEmpty()) {
        Optional<Token> resolved = Token.fromText(tokenText);
        if (resolved.isEmpty()) {
          warn("ignoring entry '%s' in '%s:...' (unknown token '%s').", raw, key.text, tokenText);
          return Optional.empty();
        }
        token = resolved.get();
      }

      Token annotation = null;
      if (annotationText != null) {
        Optional<Token> resolved = Token.fromText(annotationText);
        if (resolved.isEmpty() || !key.acceptsAnnotation(resolved.get())) {
          warn(
            "ignoring entry '%s' in '%s:...' ('%s' is not a valid annotation here).",
            raw, key.text, annotationText
          );
          return Optional.empty();
        }
        annotation = resolved.get();
      }

      if (token != null && token != Token.ALL) {
        boolean isMetric = key.acceptsMetric(token);
        boolean isBehavior = key.acceptsBehavior(token);

        if (annotation != null && isBehavior) {
          warn(
            "ignoring '%s@%s' in '%s:...': behavior token '%s' cannot be annotated.",
            token.text, annotation.text, key.text, token.text
          );
          return Optional.empty();
        }
        if (!isMetric && !isBehavior) {
          warn("ignoring token '%s', not valid for '%s:...'.", token.text, key.text);
          return Optional.empty();
        }
      }

      return Optional.of(new Entry(token, annotation));
    }

    /**
     * Splits on {@code '@'} into (token text, annotation text). A raw
     * entry with none yields a single-element list; one with more than
     * one {@code '@'} yields an empty list, signalling "malformed" to the
     * caller.
     */
    private static List<String> splitOnAt(String raw) {
      int first = raw.indexOf('@');
      if (first < 0) {
        return List.of(raw);
      }
      if (raw.indexOf('@', first + 1) >= 0) {
        return List.of();
      }
      return List.of(raw.substring(0, first), raw.substring(first + 1));
    }
  }
}
