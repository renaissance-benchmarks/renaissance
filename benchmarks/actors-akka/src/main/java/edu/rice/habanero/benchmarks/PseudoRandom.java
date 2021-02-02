package edu.rice.habanero.benchmarks;

/*
 * A simple random generator
 * which generates numbers in the range of 0-65535 and 0.0-1.0
 * Added to improves comparability between programming languages.
 */
public class PseudoRandom {
  private long value;

  public PseudoRandom(long value) {
    this.value = value;
  }

  public PseudoRandom() {
    this.value = 74755;
  }

  public long nextLong() {
    value = ((value * 1309) + 13849) & 65535;
    return value;
  }

  public int nextInt() {
    return ((int) nextLong());
  }

  public double nextDouble() {
    return 1.0 / (nextLong() + 1);
  }

  public int nextInt(int exclusive_max) {
    return nextInt() % exclusive_max;
  }
}
