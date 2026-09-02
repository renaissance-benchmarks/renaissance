package org.renaissance.gameoflife;

abstract class BitmaskRule implements Rule {
  // bit i means "next state for n=i neighbors".
  // Subclasses each override `nextState` with an identical body so all rules execute the
  // same arithmetic and bytecode shape, but JIT sees five different method entries
  protected final int birthMask;
  protected final int surviveMask;

  BitmaskRule(int birthMask, int surviveMask) {
    this.birthMask = birthMask;
    this.surviveMask = surviveMask;
  }
}
