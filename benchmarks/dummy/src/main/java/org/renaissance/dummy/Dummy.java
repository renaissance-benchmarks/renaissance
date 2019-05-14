package org.renaissance.dummy;

import org.renaissance.Benchmark;
import org.renaissance.Config;
import org.renaissance.License;
import org.renaissance.RenaissanceBenchmark;

import static org.renaissance.Benchmark.Licenses;

@Benchmark.Summary("A dummy benchmark which only serves to test the harness.")
@Licenses(License.MIT)
public final class Dummy extends RenaissanceBenchmark {
  @Override
  protected void runIteration(Config config) {
  }
}
