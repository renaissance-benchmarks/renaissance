package org.renaissance.gameoflife;

final class LifeWithoutDeathRule extends BitmaskRule {
  // B3/S012345678 -> once alive, stays alive
  LifeWithoutDeathRule() {
    super(1 << 3, 0x1FF);
  }

  @Override
  public boolean nextState(boolean alive, int n) {
    int mask = alive ? surviveMask : birthMask;
    return ((mask >>> n) & 1) != 0;
  }
}
