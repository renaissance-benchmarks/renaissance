package org.renaissance.dummy;

import org.renaissance.Benchmark;
import org.renaissance.BenchmarkContext;
import org.renaissance.BenchmarkResult;
import org.renaissance.BenchmarkResult.Validators;
import org.renaissance.License;

import static org.renaissance.Benchmark.*;

@Name("dummy-failing")
@Group("dummy")
@Summary("A dummy benchmark for testing the harness (fails during iteration).")
@Licenses(License.MIT)
public final class DummyFailing implements Benchmark {
  private int counter = 0;

  @Override
  public BenchmarkResult run(BenchmarkContext c) {
    counter++;
    if (counter > 1) {
      throw new AssertionError("Intentionally failing");
    } else {
      return Validators.simple("nothing", 0, 0);
    }
  }
}
