package org.renaissance.dummy;

import org.renaissance.Config;
import org.renaissance.License;
import org.renaissance.RenaissanceBenchmark;
import org.renaissance.BenchmarkResult;
import org.renaissance.ValidationException;

import static org.renaissance.Benchmark.*;

@Name("dummy-validation-failing")
@Group("dummy")
@Summary("A dummy benchmark for testing the harness (fails during validation).")
@Licenses(License.MIT)
public final class DummyValidationFailing extends RenaissanceBenchmark {
  private int counter = 0;

  @Override
  protected BenchmarkResult runIteration(Config config) {
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
