package stmbench7.operations;

import java.util.HashSet;

import stmbench7.OperationId;
import stmbench7.Setup;
import stmbench7.core.AtomicPart;

/**
 * Traversal T3, variant (c) (see the specification).
 * Simple update, update on index, long.
 */
public class Traversal3c extends Traversal3a {

	public Traversal3c(Setup oo7setup) {
		super(oo7setup);
	}

	@Override
	protected int performOperationInAtomicPart(AtomicPart part, HashSet<AtomicPart> setOfVisitedPartIds) {
		updateBuildDate(part);
		updateBuildDate(part);
		updateBuildDate(part);
		updateBuildDate(part);
		return 4;
    }
	
    @Override
    public OperationId getOperationId() {
    	return OperationId.T3c;
    }
}
