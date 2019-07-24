package org.renaissance.dummy;

import org.renaissance.Benchmark;
import org.renaissance.BenchmarkContext;
import org.renaissance.BenchmarkResult;
import org.renaissance.License;

import static org.renaissance.Benchmark.*;

@Name("dummy-setup-failing")
@Group("dummy")
@Summary("A dummy benchmark for testing the harness (fails during setup).")
@Licenses(License.MIT)
public final class DummySetupFailing implements Benchmark {
  @Override
  public void setUpBeforeAll(BenchmarkContext c) {
    throw new AssertionError("Intentionally failing");
  }

  @Override
  public BenchmarkResult runIteration(BenchmarkContext c) {
    return BenchmarkResult.simple("nothing", 0, 0);
  }
}
