package org.renaissance;

import java.util.Optional;

/**
 * Represents a run in which a fixed number of iterations are sequentially executed.
 */
public class FixedIterationsPolicy extends Policy {
  private RenaissanceBenchmark currentBenchmark;
  private Config config;
  private int iteration;
  private final int totalIterations;

  public FixedIterationsPolicy(RenaissanceBenchmark currentBenchmark, Config config) {
    this.currentBenchmark = currentBenchmark;
    this.config = config;
    this.iteration = 0;
    this.totalIterations =
      (config.repetitions() < 0) ? currentBenchmark.defaultRepetitions() : config.repetitions();
  }

  @Override
  public String description() {
    return "Runs the benchmark for a fixed number of iterations.";
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
    while (iteration < totalIterations) {
      String name = currentBenchmark.name();
      String g = currentBenchmark.mainGroup();
      if (iteration == totalIterations - 1) {
        System.out.println("====== " + name + " (" + g + "), " +
          "final iteration started ======");
      } else {
        System.out.println("====== " + name + " (" + g + "), " +
          "iteration " + iteration + " started ======");
      }
      long nanos = currentBenchmark.runIterationWithBeforeAndAfter(this, config);
      double millis = (nanos / 1000) / 1000.0;
      if (iteration == totalIterations - 1) {
        System.out.println("====== " + name + " (" + g + "), " +
          "final iteration completed (" + millis + " ms) ======");
      } else {
        System.out.println("====== " + name + " (" + g + "), " +
          "iteration " + iteration + " completed (" + millis + " ms) ======");
      }
      iteration++;
    }
    return Optional.empty();
  }
}

// private[renaissance] def execute(): Try[Unit] = {
//   while (iteration < totalIterations) {
//   val name = currentBenchmark.name
//   val g = currentBenchmark.mainGroup
//   if (iteration == totalIterations - 1) {
//   println(s"====== $name ($g), final iteration started ======")
//   } else {
//   println(s"====== $name ($g), iteration $iteration started ======")
//   }
//   val nanos = currentBenchmark.runIterationWithBeforeAndAfter(this, config)
//   val millis = (nanos / 1000).toInt / 1000.0
//   if (iteration == totalIterations - 1) {
//   println(s"====== $name ($g), final iteration completed ($millis ms) ======")
//   } else {
//   println(s"====== $name ($g), iteration $iteration completed ($millis ms) ======")
//   }
//   iteration += 1
//   }
//   Success(())
//   }
//   }

