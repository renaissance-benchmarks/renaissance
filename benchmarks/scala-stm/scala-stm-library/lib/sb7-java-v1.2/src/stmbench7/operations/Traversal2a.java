package stmbench7.operations;

import java.util.HashSet;

import stmbench7.OperationId;
import stmbench7.Setup;
import stmbench7.annotations.Transactional;
import stmbench7.annotations.Update;
import stmbench7.core.AtomicPart;

/**
 * Traversal T2, variant (a) (see the specification).
 * Simple update, long.
 */
public class Traversal2a extends Traversal1 {

    public Traversal2a(Setup oo7setup) {
    	super(oo7setup);
    }

    @Override
	@Transactional @Update
	public int performOperation() {
    	return super.performOperation();
	}
    
    @Override
    protected int performOperationInAtomicPart(AtomicPart part, HashSet<AtomicPart> setOfVisitedPartIds) {
    	if(setOfVisitedPartIds.isEmpty()) {
    		part.swapXY();
    		return 1;
    	}

    	part.nullOperation();
    	return 0;
    }
    
    @Override
    public OperationId getOperationId() {
    	return OperationId.T2a;
    }
}

