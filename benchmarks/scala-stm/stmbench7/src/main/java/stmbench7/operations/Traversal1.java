package stmbench7.operations;

import java.util.HashSet;

import stmbench7.OperationId;
import stmbench7.Setup;
import stmbench7.annotations.ReadOnly;
import stmbench7.annotations.Transactional;
import stmbench7.core.Assembly;
import stmbench7.core.AtomicPart;
import stmbench7.core.BaseAssembly;
import stmbench7.core.ComplexAssembly;
import stmbench7.core.CompositePart;
import stmbench7.core.Connection;
import stmbench7.core.Module;

/**
 * Traversal T1 (see the specification).
 * Read-only, long.
 */
public class Traversal1 extends BaseOperation {

	protected Module module;

	public Traversal1(Setup oo7setup) {
		this.module = oo7setup.getModule();
	}

	@Override
	@Transactional @ReadOnly
	public int performOperation() {
		ComplexAssembly designRoot = module.getDesignRoot();
		return traverse(designRoot);
	}

	protected int traverse(Assembly assembly) {
		if(assembly instanceof BaseAssembly) return traverse((BaseAssembly)assembly);
		else return traverse((ComplexAssembly)assembly);
	}

	protected int traverse(ComplexAssembly complexAssembly) {
		int partsVisited = 0;

		for(Assembly assembly : complexAssembly.getSubAssemblies())
			partsVisited += traverse(assembly);

		return partsVisited;
	}

	protected int traverse(BaseAssembly baseAssembly) {
		int partsVisited = 0;

		for(CompositePart component : baseAssembly.getComponents())
			partsVisited += traverse(component);

		return partsVisited;
	}

	protected int traverse(CompositePart component) {
		AtomicPart rootPart = component.getRootPart();
		HashSet<AtomicPart> setOfVisitedPartIds = new HashSet<AtomicPart>();

		return traverse(rootPart, setOfVisitedPartIds);
	}

	protected int traverse(AtomicPart part, HashSet<AtomicPart> setOfVisitedPartIds) {
		if(part == null) return 0;
		if(setOfVisitedPartIds.contains(part)) return 0;

		int result = performOperationInAtomicPart(part, setOfVisitedPartIds);

		setOfVisitedPartIds.add(part);

		for(Connection connection : part.getToConnections())
			result += traverse(connection.getDestination(), setOfVisitedPartIds);

		return result;
	}

	protected int performOperationInAtomicPart(AtomicPart part, HashSet<AtomicPart> setOfVisitedPartIds) {
		part.nullOperation();
		return 1;
	}
	
    @Override
    public OperationId getOperationId() {
    	return OperationId.T1;
    }
}
