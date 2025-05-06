package stmbench7.impl.backend;

import java.util.ArrayList;

import stmbench7.annotations.ContainedInAtomic;
import stmbench7.backend.ImmutableCollection;

/**
 * Simple implementation of a bag of objects.
 */
@ContainedInAtomic
public class BagImpl<E> extends ArrayList<E> {

	private static final long serialVersionUID = 5329072640119174542L;

	public BagImpl() {
		super();
	}
	
	public BagImpl(BagImpl<E> source) {
		super(source);
	}
	
	public ImmutableCollection<E> immutableView() {
		return new ImmutableViewImpl<E>(this);
	}
}
