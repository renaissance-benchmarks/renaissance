package org.renaissance.harness;

import org.renaissance.Benchmark;
import org.renaissance.BenchmarkResult;
import org.renaissance.BenchmarkResult.ValidationException;
import org.renaissance.Plugin.ExecutionPolicy;
import org.renaissance.core.BenchmarkDescriptor;
import org.renaissance.core.BenchmarkSuite;
import org.renaissance.core.BenchmarkSuite.SuiteBenchmarkContext;

import java.util.Locale;

/**
 * Benchmark execution driver. Captures the sequence of actions performed
 * during benchmark execution (i.e., calling the sequencing methods on a
 * benchmark and issuing notifications to event listeners) and maintains
 * execution context.
 */
final class ExecutionDriver {

  /** Context for the executed benchmark. */
  private final SuiteBenchmarkContext benchmarkContext;

  /** Name of the benchmark. */
  private final String benchmarkName;

  /** The benchmark to execute. */
  private final Benchmark benchmark;

  /** The dispatcher for execution-related events. */
  private final EventDispatcher eventDispatcher;

  /** The policy to control operation execution. */
  private final ExecutionPolicy executionPolicy;

  /** Preformatted message to print before executing the benchmark. */
  private final String beforeEachFormat;

  /** Preformatted message to print after successful benchmark operation. */
  private final String afterSuccessFormat;

  /** Preformatted message to print after failed benchmark operation. */
  private final String afterFailureFormat;

  /** The value of {@link System#nanoTime()} at VM start. */
  private final long vmStartNanos;


  private ExecutionDriver(
    final SuiteBenchmarkContext context,
    final Benchmark benchmark,
    final EventDispatcher dispatcher,
    final ExecutionPolicy policy,
    final long vmStartNanos
  ) {
    this.benchmarkContext = context;
    this.benchmark = benchmark;
    this.eventDispatcher = dispatcher;
    this.executionPolicy = policy;
    this.vmStartNanos = vmStartNanos;

    this.benchmarkName = context.benchmarkName();

    // Pre-format the message prefix so that we don't have to query
    // the static information about a benchmark over and over.
    String prefix = String.format(
      "====== %s (%s) [%s], iteration", context.benchmarkName(),
      context.benchmarkPrimaryGroup(), context.configurationName()
    );

    // Add formats for the message parts that change.
    this.beforeEachFormat = prefix + " %d started ======\n";
    this.afterSuccessFormat = prefix + " %d completed (%.3f ms) ======\n";
    this.afterFailureFormat = prefix + " %d failed (%s) ======\n";
  }


  public final void executeBenchmark() throws ValidationException {
    eventDispatcher.notifyBeforeBenchmarkSetUp(benchmarkName);

    try {
      benchmark.setUpBeforeAll(benchmarkContext);

      try {
        eventDispatcher.notifyAfterBenchmarkSetUp(benchmarkName);

        int operationIndex = 0;

        try {
          while (executionPolicy.canExecute(benchmarkName, operationIndex)) {
            printBeforeEachMessage(operationIndex);

            final long durationNanos = executeOperation(operationIndex);

            printAfterSuccessMessage(operationIndex, durationNanos);
            operationIndex++;
          }

        } catch (Throwable cause) {
          // Print failure line with a cause and rethrow the exception.
          printAfterFailureMessage(operationIndex, cause.getClass().getSimpleName());
          throw cause;

        } finally {
          // Complement the notifyAfterBenchmarkSetUp() events.
          eventDispatcher.notifyBeforeBenchmarkTearDown(benchmarkName);
        }

      } finally {
        // Complement the setUpBeforeAll() benchmark invocation.
        benchmark.tearDownAfterAll(benchmarkContext);
      }

    } finally {
      // Complement the notifyBeforeBenchmarkSetUp() events.
      eventDispatcher.notifyAfterBenchmarkTearDown(benchmarkName);
    }
  }


  private long executeOperation(final int index) throws ValidationException {
    //
    // Call the benchmark and notify listeners before the measured operation.
    // Nothing should go between the measured operation call and the timing
    // calls. If everything goes well, we notify the listeners and call the
    // benchmark after the measured operation and try to validate the result.
    // If the result is valid, we notify listeners about basic result metrics
    // and return the duration of the measured operation, otherwise an
    // exception is thrown and the method terminates prematurely.
    //
    benchmark.setUpBeforeEach(benchmarkContext);
    eventDispatcher.notifyAfterOperationSetUp(
      benchmarkName, index, executionPolicy.isLast(benchmarkName, index)
    );

    final long startNanos = System.nanoTime();
    final BenchmarkResult result = benchmark.run(benchmarkContext);
    final long durationNanos = System.nanoTime() - startNanos;

    eventDispatcher.notifyBeforeOperationTearDown(benchmarkName, index, durationNanos);
    benchmark.tearDownAfterEach(benchmarkContext);

    result.validate();

    final long uptimeNanos = startNanos - vmStartNanos;
    eventDispatcher.notifyOnMeasurementResult(benchmarkName, "uptime_ns", uptimeNanos);
    eventDispatcher.notifyOnMeasurementResult(benchmarkName, "duration_ns", durationNanos);

    eventDispatcher.notifyOnMeasurementResultsRequested(
      benchmarkName, index, eventDispatcher::notifyOnMeasurementResult
    );

    return durationNanos;
  }


  private void printBeforeEachMessage(int index) {
    System.out.printf(beforeEachFormat, index);
  }


  private void printAfterSuccessMessage(int index, long nanos) {
    final double millis = nanos / 1e6;

    // Use root locale to avoid locale-specific float formatting.
    System.out.printf(Locale.ROOT, afterSuccessFormat, index, millis);
  }

  private void printAfterFailureMessage(int index, String cause) {
    System.out.printf(afterFailureFormat, index, cause);
  }


  public static ExecutionDriver create (
    BenchmarkSuite suite, BenchmarkDescriptor descriptor,
    EventDispatcher dispatcher, ExecutionPolicy policy, long vmStartNanos
  ) {
    SuiteBenchmarkContext context = suite.createBenchmarkContext(descriptor);
    Benchmark benchmark = suite.createBenchmark(descriptor);
    return new ExecutionDriver(context, benchmark, dispatcher, policy, vmStartNanos);
  }

}
