package org.renaissance.gameoflife;

final class HighLifeRule extends BitmaskRule {
  // B36/S23
  HighLifeRule() {
    super((1 << 3) | (1 << 6), (1 << 2) | (1 << 3));
  }

  @Override
  public boolean nextState(boolean alive, int n) {
    int mask = alive ? surviveMask : birthMask;
    return ((mask >>> n) & 1) != 0;
  }
}
