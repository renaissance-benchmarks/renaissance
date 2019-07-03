package org.renaissance;

public class EmptyResult implements BenchmarkResult {
  public EmptyResult() {
  }

  @Override
  public void validate() {
    System.err.println("WARNING: This benchmark provides no result that can be validated.");
    System.err.println("         There is no way to check that no silent failure occurred.");
  }
}
