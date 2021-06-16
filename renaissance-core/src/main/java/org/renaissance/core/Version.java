package org.renaissance.core;

import java.util.Optional;

import static java.lang.Integer.compare;
import static java.lang.Math.min;
import static java.util.Arrays.stream;
import static java.util.Objects.requireNonNull;
import static java.util.stream.Collectors.joining;

/**
 * Represents a {@link Comparable} version specifier.
 * <p>
 * The class is immutable and serves mainly for expressing and checking
 * requirements on JVM specification version. As such, we only support
 * a simple number-based version scheme with one or more components
 * separated by dots ('.'). The numbers must be non-negative and no
 * component can be empty.
 * <p>
 * Note that we do not use {@code java.lang.Runtime.Version} because it
 * was introduced in Java 9 and we still support Java 8.
 */
public final class Version implements Comparable<Version> {
  private final int[] components;

  Version(int[] components) {
    this.components = components;
  }

  /** Creates a {@link Version} from a version string. */
  public static Version parse(String version) {
    final String[] parts = version.split("[.]");
    try {
      final int[] components = stream(parts).mapToInt(Integer::parseInt).toArray();

      // Check for negative numbers.
      if (stream(components).anyMatch(c -> c < 0)) {
        throw new IllegalArgumentException("illegal version format");
      }

      return new Version(components);

    } catch (NumberFormatException e) {
      throw new IllegalArgumentException("illegal version format", e);
    }
  }


  @Override
  public String toString() {
    return stream(components)
      .mapToObj(Integer::toString)
      .collect(joining("."));
  }


  @Override
  public int compareTo(Version that) {
    final int thisComponentCount = this.components.length;
    final int thatComponentCount = requireNonNull(that).components.length;

    int componentCount = min(thisComponentCount, thatComponentCount);
    for (int i = 0; i < componentCount; i++) {
      final int thisComponent = this.components[i];
      final int thatComponent = that.components[i];

      if (thisComponent != thatComponent) {
        return compare(thisComponent, thatComponent);
      }
    }

    return compare(thisComponentCount, thatComponentCount);
  }

  public int compareTo(Optional<Version> maybeThat) {
    return maybeThat.map(this::compareTo).orElse(0);
  }

  static void main(String[] args) {
    // TODO Convert to a proper test.
    String[] stringVersions = { "0", "0.1", "0.20", "1.2", "1.2.3", "1.8", "1.10.4", "11" };
    Version[] versions = stream(stringVersions).map(Version::parse).toArray(Version[]::new);
    stream(versions).forEach(System.out::println);

    for (int i = 0; i < versions.length; i++) {
      Version v1 = versions[i];
      for (int j = 0; j < versions.length; j++) {
        Version v2 = versions[j];
        int expected = compare(i, j);
        int actual = v1.compareTo(v2);
        System.out.printf(
          "%s, %s compareTo %s = %d, expected %d\n",
          expected == actual ? "pass" : "fail", v1, v2, actual, expected
        );
      }
    }
  }

}
