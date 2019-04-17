package stmbench7.impl.deucestm;

import stmbench7.OperationExecutor;
import stmbench7.core.Operation;
import stmbench7.core.OperationFailedException;

public class DeuceSTMOperationExecutor implements OperationExecutor {

	private final Operation op;
	
	public DeuceSTMOperationExecutor(Operation op) {
		this.op = op;
	}
    
        @org.deuce.Atomic
	public int execute() throws OperationFailedException {
		return op.performOperation();
	}

	public int getLastOperationTimestamp() {
		return 0;
	}

}
