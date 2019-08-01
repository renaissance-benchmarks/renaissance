package org.renaissance;

import org.renaissance.util.DirUtils;

import java.nio.file.Path;

/**
 * Represents a benchmark execution context. Provides a benchmark with access
 * to harness services. This includes access to benchmark-specific configuration
 * values and resources, information about current repetition, etc.
 */
public interface BenchmarkContext {



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
