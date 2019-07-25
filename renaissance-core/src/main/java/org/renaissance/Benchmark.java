package org.renaissance;

import java.lang.annotation.Documented;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;

public interface Benchmark {

  /**
   * Name of the benchmark. Defaults to kebab-case variant of the benchmark's
   * class name (without the package prefix). For example, the default name for
   * a class named {@code LittleBigBench} will be {@code little-big-bench}.
   */
  @Documented
  @Retention(RetentionPolicy.RUNTIME)
  @interface Name {

    String value();

  }


  /**
   * Name of the group the benchmark belongs to. Defaults to dash-separated
   * package names under org.renaissance. For example, the group name for a
   * benchmark class in the {@code org.renaissance.jdk.concurrent} package
   * will default to {@code jdk-concurrent}.
   */
  @Documented
  @Retention(RetentionPolicy.RUNTIME)
  @interface Group {

    String value();

  }


  /**
   * A brief (one-line) summary description of a benchmark. Default not set.
   */
  @Documented
  @Retention(RetentionPolicy.RUNTIME)
  @interface Summary {

    String value();

  }


  /**
   * Long description of a benchmark. Default not set.
   */
  @Documented
  @Retention(RetentionPolicy.RUNTIME)
  @interface Description {

    String value();

  }


  /**
   * Benchmark licenses. These are used to determine compatibility of a
   * benchmark with Renaissance distributions. Defaults to
   * {@link License#MIT MIT} if not set.
   */
  @Documented
  @Retention(RetentionPolicy.RUNTIME)
  public @interface Licenses {

    License[] value();

  }


  /**
   * Default number of benchmark repetitions. Determines how many times a
   * benchmark needs to be executes before a human can observe somewhat stable
   * results. This number does <b>NOT</b> guarantee completion of the benchmark
   * warmup phase and cannot be considered sufficient for heavy-duty statistical
   * evaluation. Defaults to 20 if not set.
   */
  @Documented
  @Retention(RetentionPolicy.RUNTIME)
  public @interface Repetitions {

    int value();

  }

  //

  /**
   * Called once before the first execution of a benchmark. This should be
   * used to initialize the part of benchmark state that remains unchanged
   * between repeated executions of the benchmark operation.
   */
  // TODO: void setUp(BenchmarkContext context)
  default void setUpBeforeAll(BenchmarkContext context) {}


  /**
   * Called before each (repeated) execution of a benchmark operation. This
   * should be used to initialize the part of benchmark state that is specific
   * to each execution of the benchmark operation.
   */
  // TODO: void setUpOperation(BenchmarkContext context);
  default void beforeIteration(BenchmarkContext context) {}


  /**
   * Executes the benchmark operation.
   *
   * @return instance of {@link BenchmarkResult} which supports validation
   */
  // TODO: BenchmarkResult operation(BenchmarkContext context);
  BenchmarkResult runIteration(BenchmarkContext context);


  /**
   * Called after each (repeated) execution of a benchmark operation. A dual
   * method to {@link #beforeOperation(BenchmarkContext)}, which should be used to
   * clean-up state changes due to execution of the benchmark operation. In
   * particular, the benchmark must ensure that resources are not leaked during
   * repeated execution of the benchmark operation.
   */
  // TODO void tearDownOperation(BenchmarkContext context);
  default void afterIteration(BenchmarkContext context) {}


  /**
   * Called once after the last execution of a benchmark. A dual method to
   * {@link #tearDown(BenchmarkContext)}, which should be used to clean up parts
   * of benchmark state that could leak resources.
   */
  // TODO: void tearDown(BenchmarkContext context);
  default void tearDownAfterAll(BenchmarkContext context) {}

}
