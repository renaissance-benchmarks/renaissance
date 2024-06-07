package stmbench7.impl.backend;

import java.util.TreeSet;

import stmbench7.backend.LargeSet;

/**
 * A simple implementation of a large-size set
 * (used by CompositePart objects).
 * This default implementation is NOT thread-safe.
 */
public class LargeSetImpl<E extends Comparable<E>> extends TreeSet<E> implements LargeSet<E> {

	private static final long serialVersionUID = -6991698966590705390L;

	public LargeSetImpl() {
		super();
	}
	
	public LargeSetImpl(LargeSetImpl<E> source) {
		super(source);
	}

	// The following methods are needed because TreeSet<E>
	// implements contains(Object) and remove(Object)
	// instead of contains(E) and remove(E).
	
	public boolean contains(E element) {
		return super.contains(element);
	}

	public boolean remove(E element) {
		return super.remove(element);
	}
}
