package org.renaissance;

/**
 * Represents the result of one benchmark execution. Each benchmark should
 * return a result the validity of which can be checked. The harness does not
 * care too much about the content, only that it can ask the benchmark to
 * validate its own result. A benchmark should store all necessary information
 * in the object implementing this interface.
 */
public interface BenchmarkResult {

  /**
   * Validates this benchmark result. Benchmarks are not expected to fail, but
   * if the result is invalid, throws this method must throw an exception
   * exception with an error message providing details on why the validation
   * failed.
   *
   * @throws ValidationException if the result is invalid.
   */
  void validate() throws ValidationException;
}
