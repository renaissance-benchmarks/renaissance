package stmbench7.backend;

import stmbench7.annotations.Atomic;
import stmbench7.annotations.ReadOnly;
import stmbench7.annotations.Update;

/**
 * A large set: of the size in the order of at least
 * a few hundreds of elements. Used by a composite part
 * to hold the set of child atomic parts, and by the
 * AtomicPart.buildDate index to hold all atomic parts
 * with the same build date.
 */
@Atomic
public interface LargeSet<E extends Comparable<E>> extends Iterable<E> {

	@Update
	boolean add(E element);
	
	@Update
	boolean remove(E element);
	
	@ReadOnly
	boolean contains(E element);
	
	@ReadOnly
	int size();
}
