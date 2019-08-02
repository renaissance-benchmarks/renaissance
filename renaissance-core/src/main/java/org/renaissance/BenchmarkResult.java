package org.renaissance;

import java.util.Arrays;
import java.util.List;
import java.util.Objects;
import java.util.Set;
import java.util.function.Function;
import java.util.function.LongBinaryOperator;
import java.util.function.ToLongFunction;
import java.util.stream.Collectors;
import java.util.stream.LongStream;
import java.util.stream.Stream;

import static java.util.stream.Collectors.toList;

/**
 * Represents the result of one benchmark execution. Each benchmark should
 * return a result the validity of which can be checked. The harness does not
 * care too much about the content, only that it can ask the benchmark to
 * validate its own result. A benchmark should store all necessary information
 * in the object implementing this interface.
 */
@FunctionalInterface
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

  //

  @Deprecated
  static BenchmarkResult dummy(Object... objects) {
    assert objects != null;

    return () -> {
      Arrays.fill(objects, null);

      System.err.println("WARNING: This benchmark provides no result that can be validated.");
      System.err.println("         There is no way to check that no silent failure occurred.");
    };
  }


  /**
   * Creates a simple {@link BenchmarkResult} which tests two
   * {@code long} values for equality.
   *
   * @param name The name of the result (shown in the failure error message).
   * @param expected The expected value.
   * @param actual The actual value.
   * @return New {@link BenchmarkResult} instance.
   */
  static BenchmarkResult simple(
    final String name, final long expected, final long actual
  ) {
      return () -> assertEquals(expected, actual, name);
  }


  /**
   * Creates a simple {@link BenchmarkResult} which tests two
   * {@code double} values for equality.
   *
   * @param name The name of the result (shown in the failure error message).
   * @param expected The expected value.
   * @param actual The actual value.
   * @return New {@link BenchmarkResult} instance.
   */
  static BenchmarkResult simple(
    final String name, final double expected, final double actual, final double epsilon
  ) {
    return () -> assertEquals(expected, actual, epsilon, name);
  }


  /**
   * Creates a simple hashing {@link BenchmarkResult} which computes the hash
   * of the string representation of all objects in the given {@link List} and
   * compares it to the expected hash value.
   *
   * @param expected The expected hash value.
   * @param objects The {@link List} of objects to be hashed.
   * @return New {@link BenchmarkResult} instance.
   */
  static BenchmarkResult hashing(String expected, List<?> objects) {
    assert expected != null;
    assert objects != null;

    return () -> {
      LongBinaryOperator hashFunc = (l, r) -> l * 31 + r;

      Function<LongStream, Long> streamHasher =
        s -> s.reduce(hashFunc).getAsLong();

      ToLongFunction<String> stringHasher =
        s -> streamHasher.apply(s.chars().mapToLong(i -> i));

      Function<List<?>, Stream<String>> asStrings =
        l -> l.stream().map(o -> Objects.toString(o, "null"));

      long hash = streamHasher.apply(asStrings.apply(objects).mapToLong(stringHasher));
      String actual = String.format("%16x", hash);
      assertEquals(expected, actual, "object hash");
    };
  }


  /**
   * Creates a simple hashing {@link BenchmarkResult} which computes the hash
   * of the string representation of all objects in the given {@link Set} and
   * compares it to the expected hash value.
   * <p>
   * In contrast to the {@link #hashing(String, List)} factory method, this
   * one sorts the string representation of the objects in the set before
   * computing the hash value.
   *
   * @param expected The expected hash value.
   * @param objects The {@link Set} of objects to be hashed.
   * @return New {@link BenchmarkResult} instance.
   */
  static BenchmarkResult hashing(String expected, Set<?> objects) {
    assert expected != null;
    assert objects != null;

    return () -> {
      List<String> sorted = objects.stream()
        .map(o -> Objects.toString(o, "null"))
        .sorted().collect(toList());

      hashing(expected, sorted).validate();
    };
  }


  /**
   * Creates a {@link BenchmarkResult} composite which takes multiple
   * {@link BenchmarkResult} instances and validates only if all the
   * other results validate.
   *
   * @param results The partial results making up this {@link BenchmarkResult}
   * @return New {@link BenchmarkResult} instance.
   */
  static BenchmarkResult compound(final BenchmarkResult... results) {
    assert results != null;

    return () -> {
      for (final BenchmarkResult result : results) {
        result.validate();
      }
    };
  }

  //

  static void assertEquals(
    int expected, int actual, String subject
  ) throws ValidationException {
    if (expected != actual) {
      throw new ValidationException(String.format(
        "%s: expected %d but got %d", subject, expected, actual
      ));
    }
  }


  static void assertEquals(
    double expected, double actual, double epsilon, String subject
  ) throws ValidationException {
    if (((expected + epsilon) < actual) || ((expected - epsilon) > actual)) {
      throw new ValidationException(String.format(
        "%s: expected %.5f +- %.5f but got %.5f",
        subject, expected, epsilon, actual
      ));
    }
  }


  static void assertEquals(
    Object expected, Object actual, String subject
  ) throws ValidationException {
    if (!expected.equals(actual)) {
      throw new ValidationException(String.format(
        "%s: expected %s but got %s", subject, expected, actual
      ));
    }
  }

  //

  /**
   * Indicates that a benchmark result failed to validate.
   */
  final class ValidationException extends Exception {
    public ValidationException(String message) {
        super(message);
    }
  }

}
