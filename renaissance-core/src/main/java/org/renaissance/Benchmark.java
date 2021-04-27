package org.renaissance;

import org.renaissance.core.Version;

import java.lang.annotation.Documented;
import java.lang.annotation.ElementType;
import java.lang.annotation.Repeatable;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * Represents a Renaissance benchmark. Defines the methods that need to be
 * implemented by each benchmark and serves as a name space for benchmark
 * meta-data annotations.
 * <p>
 * Each benchmark must provide at least the {@link #run(BenchmarkContext) run} method,
 * which implements the measured part of the workload represented by the benchmark.
 * Other methods are optional and should be used to ensure that the measured operation
 * only contains relevant computation and that the benchmark does not leak resources.
 * <p>
 * All {@link Benchmark} methods receive an instance of {@link BenchmarkContext}
 * as an argument, which allows them to query values of configurable parameters,
 * retrieve distribution JAR resources, or ask for harness-managed temporary
 * directories.
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
   * Container for {@link Group} annotations. Does not have to be
   * used explicitly since Java 8 which introduced the {@link Repeatable}
   * annotation. However, older Scala versions do not support annotations
   * types tagged as {@link Repeatable}, therefore the container type has
   * to be used explicitly.
   */
  @Documented
  @Target(ElementType.TYPE)
  @Retention(RetentionPolicy.RUNTIME)
  @interface Groups {
    Group[] value() default {};
  }


  /**
   * Name of the group the benchmark belongs to. Defaults to dash-separated
   * package names under org.renaissance. For example, the group name for a
   * benchmark class in the {@code org.renaissance.jdk.concurrent} package
   * will default to {@code jdk-concurrent}.
   */
  @Documented
  @Target(ElementType.TYPE)
  @Repeatable(Groups.class)
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


  /**
   * The minimum JVM specification version required (inclusive).
   * <p>
   * Indicates that a benchmark requires a JVM with a specification version
   * greater than or equal to the given minimum. If the underlying JVM does
   * not meet the requirement, the benchmark will be excluded from execution
   * and (raw) listing.
   * <p>
   * Version numbers can only consist of one or more non-negative integers
   * separated by dots ('.'), e.g., {@code "1.8"}, or {@code "11"}.
   * <p>
   * Defaults to {@code "1.8"} if unspecified.
   */
  @Documented
  @Target(ElementType.TYPE)
  @Retention(RetentionPolicy.RUNTIME)
  @interface RequiresJvm {
    String value();
  }


  /**
   * The maximum JVM specification version supported (inclusive).
   * <p>
   * Indicates that a benchmark supports a JVM with a specification version
   * lower than or equal to the given maximum. If the underlying JVM does
   * not meet the requirement, the benchmark will be excluded from execution
   * and (raw) listing.
   * <p>
   * Version numbers can only consist of one or more non-negative integers
   * separated by dots ('.'), e.g., {@code "1.8"}, or {@code "11"}.
   * <p>
   * If unspecified, the maximum JVM specification version is unbounded.
   */
  @Documented
  @Target(ElementType.TYPE)
  @Retention(RetentionPolicy.RUNTIME)
  @interface SupportsJvm {
    String value();
  }

  //

  /**
   * Called once before the first execution of the benchmark's measured operation.
   * This should be used to initialize the benchmark state that remains unchanged
   * between repeated executions of the measured operation.
   */
  default void setUpBeforeAll(BenchmarkContext context) {}


  /**
   * Called before each execution of the benchmark's measured operation. This
   * should be used to initialize the benchmark state specific to each execution
   * of the measured operation.
   */
  default void setUpBeforeEach(BenchmarkContext context) {}


  /**
   * Executes the benchmark's measured operation. Returns a {@link BenchmarkResult}
   * instance which is later used by the harness to validate the result (outside the
   * measurement block). Any computation related to benchmark validation must be
   * performed in the {@link BenchmarkResult#validate() validate} method, not in
   * this method.
   *
   * @return An instance of {@link BenchmarkResult}.
   */
  BenchmarkResult run(BenchmarkContext context);


  /**
   * Called after each execution of the benchmark's measured operation. This is a
   * pair method to {@link #setUpBeforeEach(BenchmarkContext) setUpBeforeEach}, which
   * should be used to clean-up benchmark state specific to each execution of the
   * measured operation. In particular, the benchmark must ensure that no resources are
   * leaked during repeated execution of the measured operation.
   */
  default void tearDownAfterEach(BenchmarkContext context) {}


  /**
   * Called once after the last execution of the benchmark's measured operation. A pair
   * method to {@link #setUpBeforeAll(BenchmarkContext) setUpBeforeAll}, which should
   * be used to clean up benchmark state that could cause resource leaks.
   */
  default void tearDownAfterAll(BenchmarkContext context) {}

}
