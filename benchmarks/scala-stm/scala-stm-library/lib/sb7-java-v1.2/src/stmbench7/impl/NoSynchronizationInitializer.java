package stmbench7.impl;

import stmbench7.OperationExecutorFactory;
import stmbench7.SynchMethodInitializer;
import stmbench7.ThreadFactory;
import stmbench7.annotations.Immutable;
import stmbench7.backend.BackendFactory;
import stmbench7.core.DesignObjFactory;
import stmbench7.impl.backend.BackendFactoryImpl;
import stmbench7.impl.core.DesignObjFactoryImpl;

/**
 * An initializer that provides non-thread-safe (default)
 * factories. Should normally be used only with a single thread.
 */
@Immutable
public class NoSynchronizationInitializer implements SynchMethodInitializer {

	public BackendFactory createBackendFactory() {
		return new BackendFactoryImpl();
	}

	public DesignObjFactory createDesignObjFactory() {
		return new DesignObjFactoryImpl();
	}

	public OperationExecutorFactory createOperationExecutorFactory() {
		return new DefaultOperationExecutorFactory();
	}

	public ThreadFactory createThreadFactory() {
		return new DefaultThreadFactory();
	}
}
