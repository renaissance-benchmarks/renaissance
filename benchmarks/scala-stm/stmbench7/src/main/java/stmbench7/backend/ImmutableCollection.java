package stmbench7.backend;

import stmbench7.annotations.Immutable;

/**
 * Represents a read-only view of a collection of elements.
 */
@Immutable
public interface ImmutableCollection<E> extends Iterable<E> {
	
	int size();
	boolean contains(E element); // not necessarily efficient!
	public ImmutableCollection<E> clone();
}
