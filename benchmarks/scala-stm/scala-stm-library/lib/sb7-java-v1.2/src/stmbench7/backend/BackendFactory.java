package stmbench7.backend;

import stmbench7.annotations.Immutable;

/**
 * Creates the structures of the benchmark backend: indexes,
 * id pools, and large sets.
 */
@Immutable
public abstract class BackendFactory {

	public static BackendFactory instance = null;
	
	public static void setInstance(BackendFactory newInstance) {
		instance = newInstance;
	}
	
	public abstract <E extends Comparable<E>> LargeSet<E> createLargeSet();
	public abstract <K extends Comparable<K>, V> Index<K,V> createIndex();
	public abstract IdPool createIdPool(int maxNumberOfIds);
}
