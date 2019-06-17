package org.renaissance.dummy;

import org.renaissance.Config;
import org.renaissance.License;
import org.renaissance.RenaissanceBenchmark;
import org.renaissance.BenchmarkResult;
import org.renaissance.SimpleResult;

import static org.renaissance.Benchmark.*;

@Name("dummy")
@Group("dummy")
@Summary("A dummy benchmark which only serves to test the harness.")
@Licenses(License.MIT)
public final class Dummy extends RenaissanceBenchmark {
  @Override
  protected BenchmarkResult runIteration(Config config) {
    return new SimpleResult("nothing", 0, 0);
  }
}
