package stmbench7.impl.backend;

import stmbench7.backend.BackendFactory;
import stmbench7.backend.IdPool;
import stmbench7.backend.Index;
import stmbench7.backend.LargeSet;

/**
 * Implements methods that create objects implementing
 * interfaces defined in stmbench7.backend: Index, IdPool,
 * and LargeSet. This default implementation constructs
 * objects that are NOT thread-safe. 
 */
public class BackendFactoryImpl extends BackendFactory {

	@Override
	public <E extends Comparable<E>> LargeSet<E> createLargeSet() {
		return new LargeSetImpl<E>();
	}

	@Override
	public <K extends Comparable<K>, V> Index<K,V> createIndex() {
		return new TreeMapIndex<K,V>();
	}

	@Override
	public IdPool createIdPool(int maxNumberOfIds) {
		return new IdPoolImpl(maxNumberOfIds);
	}
}
