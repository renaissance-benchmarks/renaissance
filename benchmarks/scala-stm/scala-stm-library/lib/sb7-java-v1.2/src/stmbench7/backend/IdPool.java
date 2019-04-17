package stmbench7.backend;

import stmbench7.annotations.Atomic;
import stmbench7.annotations.Update;
import stmbench7.core.OperationFailedException;

/**
 * Implements a pool of ids of various objects of the data structure.
 * Necessary to ensure that no two objects of the same type and with
 * the same id are created by different threads, and that the data
 * structure does not grow beyond the limits defined in the Parameters
 * class.
 */
@Atomic
public interface IdPool {

	@Update
	public abstract int getId() throws OperationFailedException;

	@Update
	public abstract void putUnusedId(int id);
}