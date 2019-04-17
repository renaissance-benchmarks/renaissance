package stmbench7.operations;

import java.util.HashSet;

import stmbench7.OperationId;
import stmbench7.Setup;
import stmbench7.core.AtomicPart;

/**
 * Traversal T2, variant (b) (see the specification).
 * Simple update, long.
 */
public class Traversal2b extends Traversal2a {

	public Traversal2b(Setup oo7setup) {
		super(oo7setup);
	}
    
	@Override
	protected int performOperationInAtomicPart(AtomicPart part, HashSet<AtomicPart> setOfVisitedPartIds) {
		part.swapXY();
		return 1;
	}
	
    @Override
    public OperationId getOperationId() {
    	return OperationId.T2b;
    }
}
	
