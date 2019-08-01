package org.renaissance;

import org.renaissance.util.DirUtils;

import java.nio.file.Path;

/**
 * Represents a benchmark execution context. Provides a benchmark with access
 * to harness services. This includes access to benchmark-specific configuration
 * values and resources, information about current repetition, etc.
 */
public interface BenchmarkContext {

  /**
   * Returns the value of the given named parameter in the currently selected
   * benchmark configuration as {@code int}. The method fails (with an
   * exception) if the parameter does not exist or cannot be converted to the
   * desired type.
   *
   * @param name Parameter name.
   * @return Parameter value as {@code int} value.
   */
  int intParameter(final String name);

  /**
   * Returns the value of the given named parameter in the currently selected
   * benchmark configuration as {@code double}. The method fails (with an
   * exception) if the parameter does not exist or cannot be converted to the
   * desired type.
   *
   * @param name Parameter name.
   * @return Parameter value as {@code double} value.
   */
  double doubleParameter(final String name);

  /**
   * Returns the value of the given named parameter in the currently selected
   * benchmark configuration as {@link String}. The method fails (with an
   * exception) if the parameter does not exist.
   *
   * @param name Parameter name.
   * @return Parameter value as {@code double} value.
   */
  String stringParameter(final String name);

  //
  // File system operations
  //
  // TODO: Allow benchmarks to ask for per-bench/per-operation temp directories
  // TODO: Delete temp directories automatically after bench/operation finishes
  //
  default Path getTempDir(String name) {
    throw new UnsupportedOperationException("not implemented yet");
  }

  @Deprecated
  default Path generateTempDir(String name) {
    return DirUtils.generateTempDir(name);
  }

  @Deprecated
  default void deleteTempDir(Path dir) {
    DirUtils.deleteTempDir(dir);
  }

}
