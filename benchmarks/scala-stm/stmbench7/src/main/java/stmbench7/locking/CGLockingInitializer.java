package stmbench7.locking;

import stmbench7.OperationExecutorFactory;
import stmbench7.impl.NoSynchronizationInitializer;

/**
 * An initializer for the coarse-grained locking
 * thread synchronization.
 */
public class CGLockingInitializer extends NoSynchronizationInitializer {

	@Override
	public OperationExecutorFactory createOperationExecutorFactory() {
		return new CGLockingOperationExecutorFactory();
	}
}
