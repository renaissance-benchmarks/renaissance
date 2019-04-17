package stmbench7.operations;

import stmbench7.OperationId;
import stmbench7.Setup;
import stmbench7.annotations.Transactional;
import stmbench7.annotations.Update;
import stmbench7.core.Assembly;
import stmbench7.core.OperationFailedException;

/**
 * Short traversal ST8 (see the specification).
 * Indexed update, short.
 */
public class ShortTraversal8 extends Traversal7 {

	public ShortTraversal8(Setup oo7setup) {
		super(oo7setup);
	}
    
	@Override
	@Transactional @Update
	public int performOperation() throws OperationFailedException {
    	return super.performOperation();
	}
    	
	@Override
    protected void performOperationOnAssembly(Assembly assembly) {
    	assembly.updateBuildDate();
    }
	
    @Override
    public OperationId getOperationId() {
    	return OperationId.ST8;
    }
}
