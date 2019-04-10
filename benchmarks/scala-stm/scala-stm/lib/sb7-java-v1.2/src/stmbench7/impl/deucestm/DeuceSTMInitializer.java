package stmbench7.impl.deucestm;

import stmbench7.OperationExecutorFactory;
import stmbench7.impl.NoSynchronizationInitializer;

public class DeuceSTMInitializer extends NoSynchronizationInitializer {

	@Override
	public OperationExecutorFactory createOperationExecutorFactory() {
		return new DeuceSTMOperationExecutorFactory();
	}
}
