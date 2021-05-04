package org.renaissance.harness;

import org.renaissance.Benchmark;
import org.renaissance.BenchmarkContext;
import org.renaissance.BenchmarkParameter;
import org.renaissance.BenchmarkResult;
import org.renaissance.BenchmarkResult.ValidationException;
import org.renaissance.Plugin.ExecutionPolicy;
import org.renaissance.core.BenchmarkInfo;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Locale;

import static java.nio.file.Files.createDirectories;

/**
 * Benchmark execution driver. Captures the sequence of actions performed
 * during benchmark execution (i.e., calling the sequencing methods on a
 * benchmark and issuing notifications to event listeners) and maintains
 * execution context.
 */
final class ExecutionDriver implements BenchmarkContext {

  /** Information about the benchmark to execute. */
  private final BenchmarkInfo benchInfo;

  /** Name of the benchmark configuration to use. */
  private final String configName;

  /** Harness scratch root directory. */
  private final Path scratchRoot;

  /** The value of {@link System#nanoTime()} at VM start. */
  private final long vmStartNanos;

  /** Benchmark scratch directory. */
  private Path scratchDir;

  public ExecutionDriver(
    final BenchmarkInfo benchInfo, final String configName,
    final Path scratchRoot, final long vmStartNanos
  ) {
    this.benchInfo = benchInfo;
    this.configName = configName;
    this.scratchRoot = scratchRoot;
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
  public BenchmarkParameter parameter(String name) {
    return benchInfo.parameter(configName, name);
  }


  @Override
  public Path scratchDirectory() {
    if (scratchDir == null) {
      try {
        scratchDir = createDirectories(
          benchInfo.resolveScratchDir(scratchRoot)
        ).normalize();
      } catch (IOException e) {
        // This is a problem, fail the benchmark.
        throw new RuntimeException("failed to create benchmark scratch directory", e);
      }
    }

    return scratchDir;
  }

}
