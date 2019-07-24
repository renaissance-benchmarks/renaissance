package org.renaissance.dummy;

import org.renaissance.Config;
import org.renaissance.License;
import org.renaissance.RenaissanceBenchmark;
import org.renaissance.BenchmarkResult;

import static org.renaissance.Benchmark.*;

@Name("dummy-failing")
@Group("dummy")
@Summary("A dummy benchmark for testing the harness (fails during iteration).")
@Licenses(License.MIT)
public final class DummyFailing extends RenaissanceBenchmark {
  private int counter = 0;

  @Override
  protected BenchmarkResult runIteration(Config config) {
    counter++;
    if (counter > 1) {
      throw new AssertionError("Intentionally failing");
    } else {
      return BenchmarkResult.simple("nothing", 0, 0);
    }
  }
}
