package org.renaissance.harness;

import org.renaissance.Benchmark;
import org.renaissance.BenchmarkContext;
import org.renaissance.BenchmarkResult;
import org.renaissance.BenchmarkResult.ValidationException;
import org.renaissance.Plugin.ExecutionPolicy;
import org.renaissance.core.BenchmarkInfo;

import java.util.Locale;

/**
 * Benchmark execution driver. Captures the sequence of actions performed
 * during benchmark execution (i.e., calling the sequencing methods on a
 * benchmark and issuing notifications to event listeners) and maintains
 * execution context.
 */
final class ExecutionDriver implements BenchmarkContext {

  private final BenchmarkInfo benchInfo;

  private final String configName;

  /** The value of {@link System#nanoTime()} at VM start. */
  private final long vmStartNanos;

  public ExecutionDriver(
    final BenchmarkInfo benchInfo, final String configName,
    final long vmStartNanos
  ) {
    this.benchInfo = benchInfo;
    this.configName = configName;
    this.vmStartNanos = vmStartNanos;
  }


  public final void executeBenchmark(
    Benchmark benchmark, EventDispatcher dispatcher, ExecutionPolicy policy
  ) throws ValidationException {
    final String benchName = benchInfo.name();
    dispatcher.notifyBeforeBenchmarkSetUp(benchName);

    try {
      benchmark.setUpBeforeAll(this);

      try {
        dispatcher.notifyAfterBenchmarkSetUp(benchName);

        try {
          int opIndex = 0;

          while (policy.canExecute(benchName, opIndex)) {
            printStartInfo(opIndex, benchInfo, configName);

            final long durationNanos = executeOperation(
              opIndex, benchName, benchmark, dispatcher,
              policy.isLast(benchName, opIndex)
            );

            printEndInfo(opIndex, benchInfo, configName, durationNanos);

            opIndex++;
          }

        } finally {
          // Complement the notifyAfterBenchmarkSetUp() events.
          dispatcher.notifyBeforeBenchmarkTearDown(benchName);
        }

      } finally {
        // Complement the setUpBeforeAll() benchmark invocation.
        benchmark.tearDownAfterAll(this);
      }

    } finally {
      // Complement the notifyBeforeBenchmarkSetUp() events.
      dispatcher.notifyAfterBenchmarkTearDown(benchName);
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
    bench.setUpBeforeEach(this);
    dispatcher.notifyAfterOperationSetUp(benchName, opIndex, isLast);

    final long startNanos = System.nanoTime();
    final BenchmarkResult result = bench.run(this);
    final long durationNanos = System.nanoTime() - startNanos;

    dispatcher.notifyBeforeOperationTearDown(benchName, opIndex, durationNanos);
    bench.tearDownAfterEach(this);

    result.validate();

    final long uptimeNanos = startNanos - vmStartNanos;
    dispatcher.notifyOnMeasurementResult(benchName, "uptime_ns", uptimeNanos);
    dispatcher.notifyOnMeasurementResult(benchName, "duration_ns", durationNanos);

    dispatcher.notifyOnMeasurementResultsRequested(
      benchName, opIndex, dispatcher::notifyOnMeasurementResult
    );

    return durationNanos;
  }


  private void printStartInfo(int index, BenchmarkInfo benchInfo, String confName) {
    System.out.printf(
      "====== %s (%s) [%s], iteration %d started ======\n",
      benchInfo.name(), benchInfo.module(), confName ,index
    );
  }


  private void printEndInfo(
    int index, BenchmarkInfo benchInfo, String confName, long durationNanos
  ) {
    final double durationMillis = durationNanos / 1e6;

    // Use explicit (null) locale to avoid locale-specific float formatting
    System.out.printf(
      (Locale) null,
      "====== %s (%s) [%s], iteration %d completed (%.3f ms) ======\n",
      benchInfo.name(), benchInfo.module(), confName, index, durationMillis
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
