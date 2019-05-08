package org.renaissance.dummy;

import org.renaissance.Config;
import org.renaissance.License;
import org.renaissance.RenaissanceBenchmark;

import static org.renaissance.License.MIT;

public final class Dummy extends RenaissanceBenchmark {
  @Override
  public String description() {
    return "A dummy benchmark, which does no work. It is used only to test the harness.";
  }

  @Override
  public License[] licenses() {
    return License.create(MIT);
  }

  @Override
  protected void runIteration(Config config) {
  }
}
