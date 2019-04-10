package stmbench7.impl.deucestm;

import stmbench7.OperationExecutor;
import stmbench7.OperationExecutorFactory;
import stmbench7.core.Operation;
import stmbench7.impl.DefaultOperationExecutor;

public class DeuceSTMOperationExecutorFactory extends OperationExecutorFactory {

	@Override
	public OperationExecutor createOperationExecutor(Operation op) {
		if(op.getOperationId() != null)
			return new DeuceSTMOperationExecutor(op);
		return new DefaultOperationExecutor(op);
	}

}
