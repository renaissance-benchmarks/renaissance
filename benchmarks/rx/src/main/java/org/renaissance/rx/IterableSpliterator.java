package org.renaissance.rx;



import java.util.Spliterator;
import java.util.Spliterators;



public final class IterableSpliterator<T> {

  private IterableSpliterator() {
  }

  public static <T> Iterable<T> of(Spliterator<T> spliterator) {
    return () -> Spliterators.iterator(spliterator);
  }
}
