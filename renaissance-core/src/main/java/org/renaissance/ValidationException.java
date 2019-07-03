package org.renaissance;

public class ValidationException extends RuntimeException {
    private static final long serialVersionUID = 1L;

    public ValidationException() {
    }

    public ValidationException(String message) {
        super(message);
    }

    public ValidationException(Throwable cause) {
        super(cause);
    }

    public ValidationException(String message, Throwable cause) {
        super(message, cause);
    }

    public ValidationException(String message, Throwable cause, boolean enableSuppression, boolean writableStackTrace) {
        super(message, cause, enableSuppression, writableStackTrace);
    }

    public static void throwIfNotEqual(int expected, int actual, String subject) throws ValidationException {
      if (expected != actual) {
        String message = String.format("%s: expected %d but got %d", subject, expected, actual);
        throw new ValidationException(message);
      }
    }

    public static void throwIfNotEqual(double expected, double actual, double epsilon, String subject) throws ValidationException {
      if (((expected + epsilon) < actual) || ((expected - epsilon) > actual)) {
        String message = String.format("%s: expected %.5f +- %.5f but got %.5f", subject, expected, epsilon, actual);
        throw new ValidationException(message);
      }
    }

    public static void throwIfNotEqual(Object expected, Object actual, String subject) throws ValidationException {
      if (!expected.equals(actual)) {
        String message = String.format("%s: expected %s but got %s", subject, expected, actual);
        throw new ValidationException(message);
      }
  }
}
