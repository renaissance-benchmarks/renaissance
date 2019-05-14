package org.renaissance.dummy;

import org.renaissance.Config;
import org.renaissance.License;
import org.renaissance.RenaissanceBenchmark;

import static org.renaissance.Benchmark.*;

@Name("dummy")
@Group("dummy")
@Summary("A dummy benchmark which only serves to test the harness.")
@Licenses(License.MIT)
public final class Dummy extends RenaissanceBenchmark {
  @Override
  protected void runIteration(Config config) {
  }
}
