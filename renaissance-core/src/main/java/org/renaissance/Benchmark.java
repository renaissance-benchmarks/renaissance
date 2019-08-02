package org.renaissance;

import java.lang.annotation.*;

/**
 * Represents a Renaissance benchmark. Defines the methods that need to be
 * implemented by each benchmark and serves as a name space for benchmark
 * meta-data annotations.
 * <p>
 * Each benchmark must provide at least the {@link #runIteration(BenchmarkContext)} method,
 * which implements the measured part of the benchmark workload. Other methods are
 * optional and provide a benchmark with more fine-grained control over its
 * life-cycle.
 * <p>
 * The {@link #runIteration(BenchmarkContext)} method must return an instance
 * of {@link BenchmarkResult}, which is used by the harness to validate the
 * result of the measured operation.
 * <p>All {@link Benchmark} methods receive an instance of {@link BenchmarkContext}
 * as an argument, which allows them to query values of configurable
 * parameters, retrieve distribution JAR resources, or ask for harness-managed
 * temporary directories.
 */
public interface Benchmark {

  /**
   * Name of the benchmark. Defaults to kebab-case variant of the benchmark's
   * class name (without the package prefix). For example, the default name for
   * a class named {@code LittleBigBench} will be {@code little-big-bench}.
   */
  @Documented
  @Target(ElementType.TYPE)
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
  @Target(ElementType.TYPE)
  @Retention(RetentionPolicy.RUNTIME)
  @interface Group {
    String value();
  }


  /**
   * A brief (one-line) summary description of a benchmark. Default not set.
   */
  @Documented
  @Target(ElementType.TYPE)
  @Retention(RetentionPolicy.RUNTIME)
  @interface Summary {
    String value();
  }


  /**
   * Long description of a benchmark. Default not set.
   */
  @Documented
  @Target(ElementType.TYPE)
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
  @Target(ElementType.TYPE)
  @Retention(RetentionPolicy.RUNTIME)
  @interface Licenses {
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
  @Target(ElementType.TYPE)
  @Retention(RetentionPolicy.RUNTIME)
  @interface Repetitions {
    int value();
  }


  /**
   * Container for {@link Configuration} annotations. Does not have to be
   * used explicitly since Java 8 which introduced the {@link Repeatable}
   * annotation. However, older Scala versions do not support annotations
   * types tagged as {@link Repeatable}, therefore the container type has
   * to be used explicitly.
   */
  @Documented
  @Target(ElementType.TYPE)
  @Retention(RetentionPolicy.RUNTIME)
  @interface Configurations {
    Configuration[] value() default {};
  }


  /**
   * Defines a named benchmark configuration that a benchmark can be run with.
   * <p>
   * Each configuration must have a {@link #name() name} and consists of the
   * parameters declared using the {@link Parameter} annotation, initially set
   * to their default values.
   * <p>
   * The {@link #settings() settings} attribute is optional and allows overriding
   * the values of declared configurable parameters (if not set, the parameters
   * are left at their default values). The attribute is an array of strings,
   * each containing a single key-value pair assignment in the form
   * {@code "<parameter_name> = <parameter_value>"}, which overrides the value
   * of the given parameter. Only parameters that have been previously
   * declared using the {@link Parameter} annotation can be overriden.
   * <p>
   * The {@link #summary() summary} description is optional but recommended.
   */
  @Documented
  @Target(ElementType.TYPE)
  @Repeatable(Configurations.class)
  @Retention(RetentionPolicy.RUNTIME)
  @interface Configuration {
    String name();
    String[] settings() default {};
    String summary() default "";
  }


  /**
   * Container for {@link Parameter} annotations. Does not have to be
   * used explicitly since Java 8 which introduced the {@link Repeatable}
   * annotation. However, older Scala versions do not support annotations
   * types tagged as {@link Repeatable}, therefore the container type has
   * to be used explicitly.
   */
  @Documented
  @Target(ElementType.TYPE)
  @Retention(RetentionPolicy.RUNTIME)
  @interface Parameters {
    Parameter[] value() default {};
  }


  /**
   * Defines a configurable benchmark parameter that a benchmark can query.
   * <p>
   * Each parameter must have a name and a default value represented as
   * {@link String}. A summary description of the parameter is optional but
   * recommended. The default values of configurable parameters associated
   * with a benchmark class make up a default configuration (the configuration
   * is named {@code default} and does not need to be declared explicitly).
   */
  @Documented
  @Target(ElementType.TYPE)
  @Repeatable(Parameters.class)
  @Retention(RetentionPolicy.RUNTIME)
  @interface Parameter {
    String name();
    String defaultValue() default "";
    String summary() default "";
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
