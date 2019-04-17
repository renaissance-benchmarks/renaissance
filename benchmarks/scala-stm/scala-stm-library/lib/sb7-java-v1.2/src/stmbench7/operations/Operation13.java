package stmbench7.operations;

import stmbench7.OperationId;
import stmbench7.Setup;
import stmbench7.annotations.Transactional;
import stmbench7.annotations.Update;
import stmbench7.core.BaseAssembly;
import stmbench7.core.OperationFailedException;

/**
 * Operation OP13 (see the specification).
 * Simple update, search on index.
 */
public class Operation13 extends Operation7 {

	public Operation13(Setup oo7setup) {
		super(oo7setup);
	}
    
	@Override
	@Transactional @Update
	public int performOperation() throws OperationFailedException {
    	return super.performOperation();
	}
    
	@Override
	protected void performOperationInBaseAssembly(BaseAssembly assembly) {
		assembly.updateBuildDate();
	}
	
    @Override
    public OperationId getOperationId() {
    	return OperationId.OP13;
    }
}
