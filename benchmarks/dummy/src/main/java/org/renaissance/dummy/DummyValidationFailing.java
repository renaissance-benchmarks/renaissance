package org.renaissance.dummy;

import org.renaissance.Benchmark;
import org.renaissance.BenchmarkContext;
import org.renaissance.BenchmarkResult;
import org.renaissance.License;

import static org.renaissance.Benchmark.*;

@Name("dummy-validation-failing")
@Group("dummy")
@Summary("A dummy benchmark for testing the harness (fails during validation).")
@Licenses(License.MIT)
public final class DummyValidationFailing implements Benchmark {
  private int counter = 0;

  @Override
  public BenchmarkResult run(BenchmarkContext c) {
    counter++;
    if (counter > 1) {
      return BenchmarkResult.simple("intentional failure", 1, -1);
    } else {
      return BenchmarkResult.simple("nothing", 0, 0);
    }
  }
}
