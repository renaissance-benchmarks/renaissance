package stmbench7.operations;

import java.util.HashSet;

import stmbench7.OperationId;
import stmbench7.Setup;
import stmbench7.core.AtomicPart;

/**
 * Traversal T2, variant (c) (see the specification).
 * Simple update, long.
 */
public class Traversal2c extends Traversal2a {

	public Traversal2c(Setup oo7setup) {
		super(oo7setup);
	}
	
	@Override
	protected int performOperationInAtomicPart(AtomicPart part, HashSet<AtomicPart> setOfVisitedPartIds) {
		part.swapXY();
		part.swapXY();
		part.swapXY();
		part.swapXY();
		return 4;
	}
	
    @Override
    public OperationId getOperationId() {
    	return OperationId.T2c;
    }
}
	
