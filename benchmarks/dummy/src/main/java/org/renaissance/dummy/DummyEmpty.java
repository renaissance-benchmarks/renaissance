package org.renaissance.dummy;

import org.renaissance.Benchmark;
import org.renaissance.BenchmarkContext;
import org.renaissance.BenchmarkResult;
import org.renaissance.License;

import static org.renaissance.Benchmark.*;

@Name("dummy-empty")
@Group("dummy")
@Summary("A dummy benchmark which only serves to test the harness.")
@Licenses(License.MIT)
public final class DummyEmpty implements Benchmark {
  @Override
  public BenchmarkResult runIteration(BenchmarkContext c) {
    return BenchmarkResult.simple("nothing", 0, 0);
  }
}
