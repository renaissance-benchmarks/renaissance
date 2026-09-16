package org.renaissance.plugins.jmxmetrics;

import java.util.EnumSet;

import org.renaissance.plugins.jmxmetrics.Config.Token;

/**
 * {@link Token}-keyed collection helpers shared by {@link Config},
 * {@link Selection}, and their tests.
 */
final class Tokens {
  private Tokens() {}

  static EnumSet<Token> emptySet() {
    return EnumSet.noneOf(Token.class);
  }
}
