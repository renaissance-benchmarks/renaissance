package org.renaissance.gameoflife;

final class ConwayRule extends BitmaskRule {
  // B3/S23 -> classic Conway's Game of Life
  ConwayRule() {
    super(1 << 3, (1 << 2) | (1 << 3));
  }

  @Override
  public boolean nextState(boolean alive, int n) {
    int mask = alive ? surviveMask : birthMask;
    return ((mask >>> n) & 1) != 0;
  }
}
