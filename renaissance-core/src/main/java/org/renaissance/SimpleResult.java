package org.renaissance;

public class SimpleResult implements BenchmarkResult {
  private final String name;
  private final Object expected;
  private final Object actual;
  private final Double epsilon;

  public SimpleResult(String name, long expected, long actual) {
    assert name != null;

    this.name = name;
    this.expected = (Long) expected;
    this.actual = (Long) actual;
    this.epsilon = null;
  }

  public SimpleResult(String name, double expected, double actual, double epsilon) {
    assert name != null;

    this.name = name;
    this.expected = (Double) expected;
    this.actual = (Double) actual;
    this.epsilon = (Double) epsilon;
  }

  @Override
  public void validate() {
    assert expected != null;
    assert actual != null;

    if (epsilon != null) {
      double exp = (Double) expected;
      double act = (Double) actual;
      ValidationException.throwIfNotEqual(exp, act, epsilon, name);
      return;
    }

    ValidationException.throwIfNotEqual(expected, actual, name);
  }
}
