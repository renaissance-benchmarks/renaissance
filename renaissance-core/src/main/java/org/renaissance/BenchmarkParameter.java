package org.renaissance;

import java.util.List;
import java.util.function.Function;

/**
 * Represents the value of a benchmark parameter. Provides utility methods to
 * convert a string value into more specific types.
 */
public interface BenchmarkParameter {

  /**
   * Returns the value of this parameter as {@link String}. All values have
   * a string representation.
   *
   * @return Parameter value as {@link String}.
   */
  String value();

  /**
   * Returns the value of this parameter as {@code boolean}. Fails if the
   * parameter cannot be converted the desired type.
   *
   * @return Parameter value as {@code boolean}.
   */
  boolean toBoolean();

  /**
   * Returns the value of this parameter as {@code int}. Fails if the
   * parameter cannot be converted the desired type.
   *
   * @return Parameter value as {@code int}.
   */
  int toInteger();

  /**
   * Returns the value of this parameter as {@code int} restricted to
   * positive values. Fails if the parameter cannot be converted the
   * desired type.
   *
   * @return Parameter value as positive {@code int}.
   */
  int toPositiveInteger();

  /**
   * Returns the value of this parameter as {@code double}. Fails if the
   * parameter cannot be converted the desired type.
   *
   * @return Parameter value as {@code double}.
   */
  double toDouble();

  /**
   * Interprets the value as a comma-separated list and returns
   * a {@link List<String>} containing the elements as {@link String}
   * values with the leading and trailing whitespace removed.
   *
   * @return Parameter value as {@code double}.
   */
  List<String> toList();

  /**
   * Interprets the value as a comma-separated list and returns a
   * {@link List<T>} of typed values corresponding to individual elements.
   * The caller needs to provide a parser function which can convert the
   * string representation of each value (with leading and trailing whitespace
   * removed) to the desired type. Fails if the parameter values cannot be
   * parsed by the provided function.
   *
   * @param parser Function to parse the desired value type from string.
   * @return Parameter value as {@code double}.
   */
  <T> List<T> toList(Function<String, T> parser);

}
