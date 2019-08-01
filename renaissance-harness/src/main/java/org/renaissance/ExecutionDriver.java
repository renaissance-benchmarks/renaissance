package org.renaissance;

import org.renaissance.harness.ExecutionPolicy;
import org.renaissance.util.BenchmarkInfo;

/**
 * Benchmark execution driver. Captures the sequence of actions performed
 * during benchmark execution (i.e., calling the sequencing methods on a
 * benchmark and issuing notifications to event listeners) and maintains
 * execution context.
 */
final class ExecutionDriver implements BenchmarkContext {

  private final BenchmarkInfo benchInfo;

  private final Config config;

  private int operationIndex;


  public ExecutionDriver(
    final BenchmarkInfo benchInfo, final Config config
  ) {
    this.benchInfo = benchInfo;
    this.config = config;
  }


  public final void executeBenchmark(
    Benchmark benchmark, EventDispatcher dispatcher
  ) {
    final ExecutionPolicy policy = config.policyFactory.create(config, benchInfo);

    benchmark.setUpBeforeAll(this);

    try {
      dispatcher.notifyAfterBenchmarkSetUp(benchInfo.name());

      try {
        operationIndex = 0;

        do {
          printStartInfo(operationIndex, benchInfo);

          final long durationNanos = executeOperation(
            operationIndex, benchInfo.name(), benchmark,
            dispatcher, policy.isLastOperation()
          );

          printEndInfo(operationIndex, benchInfo, durationNanos);
          policy.registerOperation(operationIndex, durationNanos);

          operationIndex++;
        } while (policy.keepExecuting());

      } finally {
        dispatcher.notifyBeforeBenchmarkTearDown(benchInfo.name());
      }

    } finally {
      benchmark.tearDownAfterAll(this);
    }
  }


  private long executeOperation(
    final int opIndex, final String benchName, final Benchmark bench,
    final EventDispatcher dispatcher, final boolean isLast
  ) {
    //
    // Call the benchmark and notify listeners before the measured operation.
    // Nothing should go between the measured operation call and the timing
    // calls. If everything goes well, we notify the listeners and call the
    // benchmark after the measured operation and try to validate the result.
    // If the result is valid, we notify listeners about basic result metrics
    // and return the duration of the measured operation, otherwise an
    // exception is thrown and the method terminates prematurely.
    //
    final long unixTsBefore = System.currentTimeMillis();
    bench.beforeIteration(this);
    dispatcher.notifyAfterOperationSetUp(benchName, opIndex, isLast);

    final long startNanos = System.nanoTime();
    final BenchmarkResult result = bench.runIteration(this);
    final long durationNanos = System.nanoTime() - startNanos;

    dispatcher.notifyBeforeOperationTearDown(benchName, opIndex, durationNanos);
    bench.afterIteration(this);
    final long unixTsAfter = System.currentTimeMillis();

    result.validate();

    dispatcher.notifyOnBenchmarkResult(benchName, "nanos", durationNanos);
    dispatcher.notifyOnBenchmarkResult(benchName, "unixts.before", unixTsBefore);
    dispatcher.notifyOnBenchmarkResult(benchName, "unixts.after", unixTsAfter);

    return durationNanos;
  }


  void printStartInfo(int index, BenchmarkInfo benchInfo) {
    System.out.printf(
      "====== %s (%s), iteration %d started ======\n",
      benchInfo.name(), benchInfo.group(), index
    );
  }


  void printEndInfo(int index, BenchmarkInfo benchInfo, long durationNanos) {
    final double durationMillis = durationNanos / 1e6;

    System.out.printf(
      "====== %s (%s), iteration %d completed (%.3f ms) ======\n",
      benchInfo.name(), benchInfo.group(), index, durationMillis
    );
  }

  // BenchmarkContext methods

  @Override
  }


  @Override
  }


  @Override
  }

}
