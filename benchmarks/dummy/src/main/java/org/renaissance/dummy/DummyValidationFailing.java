package org.renaissance.dummy;

import org.renaissance.*;

import static org.renaissance.Benchmark.*;

@Name("dummy-validation-failing")
@Group("dummy")
@Summary("A dummy benchmark for testing the harness (fails during validation).")
@Licenses(License.MIT)
public final class DummyValidationFailing implements Benchmark {
  private int counter = 0;

  @Override
  public BenchmarkResult runIteration(BenchmarkContext c) {
    counter++;
    if (counter > 1) {
      return () -> {
        throw new ValidationException("Intentionally failing");
      };

    } else {
      return BenchmarkResult.simple("nothing", 0, 0);
    }
  }
}
