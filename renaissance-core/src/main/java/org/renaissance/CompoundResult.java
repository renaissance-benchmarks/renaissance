package org.renaissance;

public class CompoundResult implements BenchmarkResult {
  private final BenchmarkResult[] results;

  public CompoundResult(BenchmarkResult... results) {
    assert results != null;

    this.results = results;
  }
  
  @Override
  public void validate() {
    for (BenchmarkResult res : results) {
      res.validate();
    }
  }
}
