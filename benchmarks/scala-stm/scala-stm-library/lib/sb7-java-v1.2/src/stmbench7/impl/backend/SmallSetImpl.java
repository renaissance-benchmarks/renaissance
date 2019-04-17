package stmbench7.impl.backend;

import java.util.ArrayList;

import stmbench7.annotations.ContainedInAtomic;
import stmbench7.backend.ImmutableCollection;

/**
 * A simple implementation of a small-size set
 * (used by Assembly and AtomicPart objects).
 */
@ContainedInAtomic
public class SmallSetImpl<E> extends ArrayList<E> {

	private static final long serialVersionUID = 8608574819902616324L;

	public SmallSetImpl() {
		super();
	}
	
	public SmallSetImpl(SmallSetImpl<E> source) {
		super(source);
	}
	
	public boolean add(E element) {
		if(contains(element)) return false;

		super.add(element);
		return true;
	}
	
	public ImmutableCollection<E> immutableView() {
		return new ImmutableViewImpl<E>(this);
	}
}
