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
      if (act != exp) {
        if (((exp + epsilon) < act) || ((exp - epsilon) > act)) {
          throw new ValidationException(String.format(
            "Validation failed: expected %.4f +- %.5f but got %.4f (%s)",
            exp, act, name));
        }
        return;
      }
    }

    if (!expected.equals(actual)) {
      throw new ValidationException(String.format(
        "Validation failed: expected %s but got %s (%s)",
        expected, actual, name));
    }
  }
}
