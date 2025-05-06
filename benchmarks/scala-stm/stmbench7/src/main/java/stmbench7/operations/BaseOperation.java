package stmbench7.operations;

import stmbench7.OperationId;
import stmbench7.annotations.Transactional;
import stmbench7.annotations.Update;
import stmbench7.backend.BackendFactory;
import stmbench7.backend.Index;
import stmbench7.backend.LargeSet;
import stmbench7.core.AtomicPart;
import stmbench7.core.Operation;
import stmbench7.core.OperationFailedException;

/**
 * Base class for all the benchmark operations.
 */
public abstract class BaseOperation implements Operation {

	@Transactional 
	@Update
	public abstract int performOperation() throws OperationFailedException;

	public abstract OperationId getOperationId();
	
	/**
	 * The method of adding and AtomicPart to the AtomicPartBuildDateIndex is
	 * non-trivial and is used in a few places. That is why it is put here for
	 * later reuse.
	 * 
	 * At first glance, it may seem more complicated than it is necessary,
	 * but that is because we want to use only locking implemented by
	 * an Index and Set implementations.
	 */
	public static void addAtomicPartToBuildDateIndex(
			Index<Integer,LargeSet<AtomicPart>> atomicPartBuildDateIndex,
			AtomicPart atomicPart) {
		LargeSet<AtomicPart> newSet = BackendFactory.instance.<AtomicPart>createLargeSet();
		newSet.add(atomicPart);
		LargeSet<AtomicPart> sameDateSet = 
			atomicPartBuildDateIndex.putIfAbsent(atomicPart.getBuildDate(), newSet);
		if(sameDateSet != null) sameDateSet.add(atomicPart);
	}

	/**
	 * The method of removing and AtomicPart from the AtomicPartBuildDateIndex is
	 * non-trivial and is used in a few places. That is why it is put here for
	 * later reuse.
	 */
	public static void removeAtomicPartFromBuildDateIndex(
			Index<Integer,LargeSet<AtomicPart>> atomicPartBuildDateIndex,
			AtomicPart atomicPart) {
		LargeSet<AtomicPart> sameDateSet = atomicPartBuildDateIndex.get(atomicPart.getBuildDate());
		sameDateSet.remove(atomicPart);
	}
}
