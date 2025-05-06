package stmbench7.impl;

import stmbench7.OperationExecutor;
import stmbench7.OperationExecutorFactory;
import stmbench7.annotations.Immutable;
import stmbench7.core.Operation;

/**
 * Default implementation of an OperationExecutorFactory.
 * It creates an OperationExecutor that does not provide
 * any synchronization between threads.
 */
@Immutable
public class DefaultOperationExecutorFactory extends OperationExecutorFactory {

	public OperationExecutor createOperationExecutor(Operation op) {
		return new DefaultOperationExecutor(op);
	}
}
