package org.renaissance;

import java.nio.file.Path;

/**
 * Represents a benchmark execution context. Provides a benchmark with access
 * to harness services. This includes access to benchmark-specific configuration
 * values and resources, information about current repetition, etc.
 */
public interface BenchmarkContext {

  // TODO Remove when we get configurations working.
  @Deprecated
  boolean functionalTest();

  String benchmarkName();

  String benchmarkGroup();

  int operationIndex();

  //
  // File system operations
  //
  // TODO: Allow benchmarks to ask for per-bench/per-operation temp directories
  // TODO: Delete temp directories automatically after bench/operation finishes
  //
  Path getTempDir(String name);

  @Deprecated
  Path generateTempDir(String name);

  @Deprecated
  void deleteTempDir(Path dir);

  @Deprecated
  // TODO: Remove when all benchmarks return proper results
  <T> T blackHole(final T value);

}
