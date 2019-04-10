package stmbench7.operations;

import stmbench7.OperationId;
import stmbench7.Setup;
import stmbench7.annotations.Transactional;
import stmbench7.annotations.Update;
import stmbench7.core.CompositePartBuilder;
import stmbench7.core.OperationFailedException;

/**
 * Structural modification operation SM1 (see the specification).
 */
public class StructuralModification1 extends BaseOperation {

	protected CompositePartBuilder compositePartBuilder;
	
	public StructuralModification1(Setup oo7setup) {
		compositePartBuilder = oo7setup.getCompositePartBuilder();
	}

	@Override
	@Transactional @Update
	public int performOperation() throws OperationFailedException {
		compositePartBuilder.createAndRegisterCompositePart();
		return 0;
	}
	
    @Override
    public OperationId getOperationId() {
    	return OperationId.SM1;
    }
}
