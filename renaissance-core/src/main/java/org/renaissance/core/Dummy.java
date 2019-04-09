package org.renaissance.core;

import org.renaissance.Config;
import org.renaissance.RenaissanceBenchmark;

public class Dummy extends RenaissanceBenchmark {
  @Override
  public String description() {
    return "A dummy benchmark, which does no work. It is used only to test the harness.";
  }

  @Override
  protected void runIteration(Config config) {
  }
}
