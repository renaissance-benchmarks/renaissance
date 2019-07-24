package org.renaissance.dummy;

import org.renaissance.Config;
import org.renaissance.License;
import org.renaissance.RenaissanceBenchmark;
import org.renaissance.BenchmarkResult;

import static org.renaissance.Benchmark.*;

@Name("dummy-empty")
@Group("dummy")
@Summary("A dummy benchmark which only serves to test the harness.")
@Licenses(License.MIT)
public final class DummyEmpty extends RenaissanceBenchmark {
  @Override
  public BenchmarkResult runIteration(BenchmarkContext c) {
    return BenchmarkResult.simple("nothing", 0, 0);
  }
}
