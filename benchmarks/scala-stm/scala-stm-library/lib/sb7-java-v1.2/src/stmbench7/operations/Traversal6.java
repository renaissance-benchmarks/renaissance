package stmbench7.operations;

import java.util.HashSet;

import stmbench7.OperationId;
import stmbench7.Setup;
import stmbench7.core.AtomicPart;
import stmbench7.core.CompositePart;

/**
 * Traversal T6 (see the specification).
 * Read-only, long.
 */
public class Traversal6 extends Traversal1 {

	public Traversal6(Setup oo7setup) {
		super(oo7setup);
	}

	@Override
	protected int traverse(CompositePart component) {
		AtomicPart rootPart = component.getRootPart();
		return traverse(rootPart, null);
	}

	@Override
	protected int traverse(AtomicPart part, HashSet<AtomicPart> setOfVisitedPartIds) {
		return performOperationInAtomicPart(part, null);
	}

	@Override
	protected int performOperationInAtomicPart(AtomicPart part, HashSet<AtomicPart> setOfVisitedPartIds) {
		part.nullOperation();
		return 1;
	}
	
    @Override
    public OperationId getOperationId() {
    	return OperationId.T6;
    }
}
