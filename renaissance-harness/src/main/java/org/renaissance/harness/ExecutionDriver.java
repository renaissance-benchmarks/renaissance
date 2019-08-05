package org.renaissance.harness;

import org.renaissance.Benchmark;
import org.renaissance.BenchmarkContext;
import org.renaissance.BenchmarkResult;
import org.renaissance.BenchmarkResult.ValidationException;
import org.renaissance.ExecutionPolicy;
import org.renaissance.core.BenchmarkInfo;

/**
 * Benchmark execution driver. Captures the sequence of actions performed
 * during benchmark execution (i.e., calling the sequencing methods on a
 * benchmark and issuing notifications to event listeners) and maintains
 * execution context.
 */
final class ExecutionDriver implements BenchmarkContext {

  private final BenchmarkInfo benchInfo;

  private final String configName;


  public ExecutionDriver(
    final BenchmarkInfo benchInfo, final String configName
  ) {
    this.benchInfo = benchInfo;
    this.configName = configName;
  }


  public final void executeBenchmark(
    Benchmark benchmark, EventDispatcher dispatcher, ExecutionPolicy policy
  ) throws ValidationException {
    benchmark.setUpBeforeAll(this);

    try {
      dispatcher.notifyAfterBenchmarkSetUp(benchInfo.name());

      try {
        int operationIndex = 0;

        do {
          printStartInfo(operationIndex, benchInfo, configName);

          final long durationNanos = executeOperation(operationIndex, benchInfo.name(), benchmark,
            dispatcher, policy.isLastOperation()
          );

          printEndInfo(operationIndex, benchInfo, configName, durationNanos);
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
  ) throws ValidationException {
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

    dispatcher.notifyOnMeasurementResult(benchName, "nanos", durationNanos);
    dispatcher.notifyOnMeasurementResult(benchName, "unixts.before", unixTsBefore);
    dispatcher.notifyOnMeasurementResult(benchName, "unixts.after", unixTsAfter);

    dispatcher.notifyMeasurementResultsRequested(
      benchName, (metric, value) -> dispatcher.notifyOnMeasurementResult(benchName, metric, value)
    );

    return durationNanos;
  }


  private void printStartInfo(int index, BenchmarkInfo benchInfo, String confName) {
    System.out.printf(
      "====== %s (%s) [%s], iteration %d started ======\n",
      benchInfo.name(), benchInfo.group(), confName ,index
    );
  }


  private void printEndInfo(
    int index, BenchmarkInfo benchInfo, String confName, long durationNanos
  ) {
    final double durationMillis = durationNanos / 1e6;

    System.out.printf(
      "====== %s (%s) [%s], iteration %d completed (%.3f ms) ======\n",
      benchInfo.name(), benchInfo.group(), confName, index, durationMillis
    );
  }

  // BenchmarkContext methods

  @Override
  public int intParameter(String name) {
    return Integer.parseInt(stringParameter(name));
  }


  @Override
  public double doubleParameter(String name) {
    return Double.parseDouble(stringParameter(name));
  }


  @Override
  public String stringParameter(String name) {
    return benchInfo.parameter(configName, name);
  }

}
