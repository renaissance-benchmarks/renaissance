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
   * Benchmark licenses. These are used to determine to which Renaissance
   * distro the benchmark belongs. Defaults to MIT if not set.
   */
  @Documented
  @Retention(RetentionPolicy.RUNTIME)
  public @interface Licenses {

    License[] value();

  }


  /**
   * Default number of benchmark repetitions. Determines how many times a
   * benchmark needs to be executes before a human can observe somewhat stable
   * results. This number does not guarantee completion of the benchmark
   * warmup phase and is not usually sufficient for heavy-duty statistical
   * evaluation. Defaults to 20 if not set.
   */
  @Documented
  @Retention(RetentionPolicy.RUNTIME)
  public @interface Repetitions {

    int value();

  }

}
