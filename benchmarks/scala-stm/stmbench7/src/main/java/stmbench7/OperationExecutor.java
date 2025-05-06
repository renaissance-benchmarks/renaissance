package stmbench7;

import stmbench7.annotations.NonAtomic;
import stmbench7.annotations.ThreadLocal;
import stmbench7.core.OperationFailedException;

/**
 * An interface representing a class that executes a given operation.
 * Can set up a transaction and handle aborts.
 */
@NonAtomic
@ThreadLocal
public interface OperationExecutor {

	int execute() throws OperationFailedException;
	int getLastOperationTimestamp();
}
