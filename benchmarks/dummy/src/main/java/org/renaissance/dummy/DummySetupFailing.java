package org.renaissance.dummy;

import org.renaissance.Config;
import org.renaissance.License;
import org.renaissance.RenaissanceBenchmark;
import org.renaissance.BenchmarkResult;

import static org.renaissance.Benchmark.*;

@Name("dummy-setup-failing")
@Group("dummy")
@Summary("A dummy benchmark for testing the harness (fails during setup).")
@Licenses(License.MIT)
public final class DummySetupFailing extends RenaissanceBenchmark {
  @Override
  public void setUpBeforeAll(Config config) {
    throw new AssertionError("Intentionally failing");
  }

  @Override
  protected BenchmarkResult runIteration(Config config) {
    return BenchmarkResult.simple("nothing", 0, 0);
  }
}
