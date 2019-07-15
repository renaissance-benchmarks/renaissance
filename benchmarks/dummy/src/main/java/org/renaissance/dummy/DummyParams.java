package org.renaissance.dummy;

import org.renaissance.Config;
import org.renaissance.License;
import org.renaissance.RenaissanceBenchmark;
import org.renaissance.BenchmarkResult;
import org.renaissance.SimpleResult;

import static org.renaissance.Benchmark.*;

@Name("dummy-params")
@Group("dummy")
@Summary("A dummy benchmark for testing the harness (test parametrization).")
@Licenses(License.MIT)
@Configuration(name="default", values={ "fortytwo=42", "threads=1" })
@Configuration(name="large", values={ "fortytwo=42", "threads=cpu.count" })
public final class DummyParams extends RenaissanceBenchmark {
  @Override
  protected BenchmarkResult runIteration(Config config) {
    int fortytwo = config.parameter("fortytwo");
    int threads = config.parameter("threads");
    System.out.printf("Threads = %d\n", threads);
    return new SimpleResult("constant parameter", fortytwo, 42);
  }
}
