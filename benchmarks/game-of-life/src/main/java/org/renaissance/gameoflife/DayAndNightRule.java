package org.renaissance.gameoflife;

final class DayAndNightRule extends BitmaskRule {
  // B3678/S34678
  DayAndNightRule() {
    super(
      (1 << 3) | (1 << 6) | (1 << 7) | (1 << 8),
      (1 << 3) | (1 << 4) | (1 << 6) | (1 << 7) | (1 << 8)
    );
  }

  @Override
  public boolean nextState(boolean alive, int n) {
    int mask = alive ? surviveMask : birthMask;
    return ((mask >>> n) & 1) != 0;
  }
}
