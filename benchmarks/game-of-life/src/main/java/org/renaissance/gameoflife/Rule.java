package org.renaissance.gameoflife;

interface Rule {
  boolean nextState(boolean alive, int neighbors);
}
