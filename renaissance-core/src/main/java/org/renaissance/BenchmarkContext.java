package org.renaissance;

import org.renaissance.core.DirUtils;

import java.nio.file.Path;
import java.util.NoSuchElementException;

/**
 * Represents a benchmark execution context. Allows a benchmark to access
 * harness-provided utility services, such as retrieving benchmark- and
 * configuration-specific parameter values, JAR file resources, or selected
 * filesystem operations.
 */
public interface BenchmarkContext {

  /**
   * Returns the given named parameter in the currently selected benchmark
   * configuration. The method fails (with an exception) if the parameter
   * does not exist.
   *
   * @param name Parameter name.
   * @return {@link BenchmarkParameter} instance.
   * @throws NoSuchElementException if the parameter does not exist.
   */
  BenchmarkParameter parameter(final String name);


  /**
   * Provides a path to the benchmark-specific scratch directory that will be
   * deleted (or not, depending on harness settings) after the harness exits.
   * The benchmark can do whatever it wants in the subtree below the scratch
   * directory, but should not modify anything outside that subtree.
   *
   * @return {@link Path} to benchmark-specific scratch directory.
   */
  Path scratchDirectory();

}
