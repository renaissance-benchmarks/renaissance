package stmbench7.locking;

import stmbench7.OperationExecutorFactory;
import stmbench7.core.DesignObjFactory;
import stmbench7.impl.NoSynchronizationInitializer;

/**
 * An initializer for the medium-grained locking synchronization
 * method.
 */
public class MGLockingInitializer extends NoSynchronizationInitializer {

	public DesignObjFactory createDesignObjFactory() {
		return new MGLockingDesignObjFactory();
	}

	public OperationExecutorFactory createOperationExecutorFactory() {
		return new MGLockingOperationExecutorFactory();
	}
}
