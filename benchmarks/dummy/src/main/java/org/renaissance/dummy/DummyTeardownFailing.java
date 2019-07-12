package org.renaissance.dummy;

import org.renaissance.Config;
import org.renaissance.License;
import org.renaissance.RenaissanceBenchmark;
import org.renaissance.BenchmarkResult;
import org.renaissance.SimpleResult;

import static org.renaissance.Benchmark.*;

@Name("dummy-teardown-failing")
@Group("dummy")
@Summary("A dummy benchmark for testing the harness (fails during teardown).")
@Licenses(License.MIT)
public final class DummyTeardownFailing extends RenaissanceBenchmark {
  @Override
  public void tearDownAfterAll(Config config) {
    throw new AssertionError("Intentionally failing");
  }

  @Override
  protected BenchmarkResult runIteration(Config config) {
    return new SimpleResult("nothing", 0, 0);
  }
}
