package org.renaissance.gameoflife;

final class SeedsRule extends BitmaskRule {
  // B2/S -> never survives
  SeedsRule() {
    super(1 << 2, 0);
  }

  @Override
  public boolean nextState(boolean alive, int n) {
    int mask = alive ? surviveMask : birthMask;
    return ((mask >>> n) & 1) != 0;
  }
}
