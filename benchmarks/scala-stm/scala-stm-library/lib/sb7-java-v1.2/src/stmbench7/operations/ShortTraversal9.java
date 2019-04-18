package stmbench7.operations;

import java.util.HashSet;

import stmbench7.OperationId;
import stmbench7.Setup;
import stmbench7.core.AtomicPart;
import stmbench7.core.CompositePart;
import stmbench7.core.Connection;
import stmbench7.core.RuntimeError;

/**
 * Short traversal ST9 (see the specification).
 * Read-only, short.
 */
public class ShortTraversal9 extends ShortTraversal1 {

	public ShortTraversal9(Setup oo7setup) {
		super(oo7setup);
	}
	
	@Override
	protected int traverse(CompositePart component) {
		HashSet<AtomicPart> setOfVisitedPartIds = new HashSet<AtomicPart>();
		return traverse(component.getRootPart(), setOfVisitedPartIds);
	}
	
	protected int traverse(AtomicPart atomicPart, HashSet<AtomicPart> setOfVisitedPartIds) {
		if(atomicPart == null) return 0;
		if(setOfVisitedPartIds.contains(atomicPart)) return 0;

		int result = performOperationInAtomicPart(atomicPart);

		setOfVisitedPartIds.add(atomicPart);

		for(Connection connection : atomicPart.getToConnections())
			result += traverse(connection.getDestination(), setOfVisitedPartIds);

		return result;
	}

	protected int performOperationInAtomicPart(AtomicPart part) {
		part.nullOperation();
		return 1;
	}
	
	@Override
	protected int traverse(AtomicPart atomicPart) {
		throw new RuntimeError("ST9: unexpected call to traverse(AtomicPart)!");
	}
	
    @Override
    public OperationId getOperationId() {
    	return OperationId.ST9;
    }
}
