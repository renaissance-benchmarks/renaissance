package org.renaissance;

import java.util.Optional;

/**
 * Represents a run in which a fixed number of iterations are sequentially executed.
 */
public class FixedWarmupPolicy extends Policy {
  private RenaissanceBenchmark currentBenchmark;
  private Config config;
  private int iteration;
  private final int warmupSeconds;
  private final int runSeconds;

  public FixedWarmupPolicy(RenaissanceBenchmark currentBenchmark, Config config) {
    this.currentBenchmark = currentBenchmark;
    this.config = config;
    this.iteration = 0;
    this.warmupSeconds = config.warmupSeconds;
    this.runSeconds = config.runSeconds;
  }

  @Override
  public String description() {
    return "Warms up the VM by running the benchmark a fixed amount of time, " +
      "and then runs the benchmark again for some fixed amount of time (use `-w` and `-t`).";
  }

  @Override
  public RenaissanceBenchmark currentBenchmark() {
    return currentBenchmark;
  }

  public int currentIteration() {
    return iteration;
  }

  @Override
  public Optional<Throwable> execute() {
    String name = currentBenchmark.name();
    String g = currentBenchmark.mainGroup();
    long startWarmupTime = System.currentTimeMillis();
    while (System.currentTimeMillis() < startWarmupTime + warmupSeconds * 1000) {
      System.out.println("====== " + name + " (" + g + "), " +
        "warmup iteration " + iteration + " started ======");
      long nanos = currentBenchmark.runIterationWithBeforeAndAfter(this, config);
      double millis = (nanos / 1000) / 1000.0;
      System.out.println("====== " + name + " (" + g + "), " +
        "warmup iteration " + iteration + " completed (" + millis + " ms) ======");
      iteration++;
    }
    iteration = 0;
    long startRunTime = System.currentTimeMillis();
    while (System.currentTimeMillis() < startRunTime + runSeconds * 1000) {
      System.out.println("====== " + name + " (" + g + "), " +
        "iteration " + iteration + " started ======");
      long nanos = currentBenchmark.runIterationWithBeforeAndAfter(this, config);
      double millis = (nanos / 1000) / 1000.0;
      System.out.println("====== " + name + " (" + g + "), " +
        "iteration " + iteration + " completed (" + millis + " ms) ======");
      iteration++;
    }
    return Optional.empty();
  }
}
