package org.renaissance.rx;



import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.Set;

import static java.util.Arrays.stream;
import static java.util.Objects.requireNonNull;
import static java.util.stream.Collectors.toSet;


public class Scrabble {

  static class MutableLong {
    long value;

    long get() {
      return value;
    }

    MutableLong set(long l) {
      value = l;
      return this;
    }

    MutableLong incAndSet() {
      value++;
      return this;
    }

    MutableLong add(MutableLong other) {
      value += other.value;
      return this;
    }
  }

  interface Wrapper<T> {
    T get();

    default Wrapper<T> set(T t) {
      return () -> t;
    }
  }

  interface IntWrapper {
    int get();

    default IntWrapper set(int i) {
      return () -> i;
    }

    default IntWrapper incAndSet() {
      return () -> get() + 1;
    }
  }

  interface LongWrapper {
    long get();

    default LongWrapper set(long l) {
      return () -> l;
    }

    default LongWrapper incAndSet() {
      return () -> get() + 1L;
    }

    default LongWrapper add(LongWrapper other) {
      return () -> get() + other.get();
    }
  }

  public static final int[] letterScores = {
    // a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p,  q, r, s, t, u, v, w, x, y,  z
    1, 3, 3, 2, 1, 4, 2, 4, 1, 8, 5, 1, 3, 1, 1, 3, 10, 1, 1, 1, 1, 4, 4, 8, 4, 10};

  public static final int[] scrabbleAvailableLetters = {
    // a, b, c, d,  e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z
    9, 2, 2, 1, 12, 2, 3, 2, 9, 1, 1, 4, 2, 6, 8, 2, 1, 6, 4, 6, 4, 2, 2, 1, 2, 1};


  public Set<String> scrabbleWords;
  public Set<String> shakespeareWords;

  public Scrabble(String scrabblePath, String shakespearePath) {
    scrabbleWords = resourceAsLowerCaseWords(scrabblePath);
    shakespeareWords = resourceAsLowerCaseWords(shakespearePath);
  }

  public Set<String> resourceAsLowerCaseWords(String resourceName) {
    try (
      BufferedReader reader = getResourceReader(resourceName)
    ) {
      return reader.lines()
        .flatMap(s -> stream(s.split("\\s+")))
        .map(String::trim)
        .filter(s -> !s.isEmpty())
        .map(String::toLowerCase)
        .collect(toSet());
    } catch (IOException e) {
      throw new RuntimeException(e);
    }
  }

  private BufferedReader getResourceReader(String resourceName) {
    return new BufferedReader(new InputStreamReader(
      requireNonNull(getClass().getResourceAsStream(resourceName)))
    );
  }

}
