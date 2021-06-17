package org.renaissance.dummy;

import org.renaissance.Benchmark;
import org.renaissance.BenchmarkContext;
import org.renaissance.BenchmarkResult;
import org.renaissance.BenchmarkResult.Validators;
import org.renaissance.License;

import static org.renaissance.Benchmark.*;

@Name("dummy-empty")
@Group("dummy")
@Summary("A dummy benchmark which only serves to test the harness.")
@Licenses(License.MIT)
@Configuration(name = "test")
public final class DummyEmpty implements Benchmark {
  @Override
  public BenchmarkResult run(BenchmarkContext c) {
    return Validators.simple("nothing", 0, 0);
  }
}
