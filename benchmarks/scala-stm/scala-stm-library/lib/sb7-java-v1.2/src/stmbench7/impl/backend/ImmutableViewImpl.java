package stmbench7.impl.backend;

import java.util.ArrayList;
import java.util.Iterator;

import stmbench7.backend.ImmutableCollection;

public class ImmutableViewImpl<E> implements ImmutableCollection<E>, Cloneable {

	private final ArrayList<E> elements;
	
	public ImmutableViewImpl(ArrayList<E> elements) {
		this.elements = elements;
	}
	
	public boolean contains(E element) {
		return elements.contains(element);
	}

	public int size() {
		return elements.size();
	}

	public Iterator<E> iterator() {
		return elements.iterator();
	}
	
	@SuppressWarnings("unchecked")
	public ImmutableCollection<E> clone() {
		return new ImmutableViewImpl<E>((ArrayList<E>) elements.clone());
	}
}