package org.renaissance.dummy;

import org.renaissance.Benchmark;
import org.renaissance.BenchmarkContext;
import org.renaissance.BenchmarkResult;
import org.renaissance.BenchmarkResult.Validators;
import org.renaissance.License;

import static org.renaissance.Benchmark.*;

@Name("dummy-teardown-failing")
@Group("dummy")
@Summary("A dummy benchmark for testing the harness (fails during teardown).")
@Licenses(License.MIT)
public final class DummyTeardownFailing implements Benchmark {
  @Override
  public void tearDownAfterAll(BenchmarkContext c) {
    throw new AssertionError("Intentionally failing");
  }

  @Override
  public BenchmarkResult run(BenchmarkContext c) {
    return Validators.simple("nothing", 0, 0);
  }
}
