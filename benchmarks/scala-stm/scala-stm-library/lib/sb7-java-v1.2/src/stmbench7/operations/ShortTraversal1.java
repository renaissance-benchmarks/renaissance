package stmbench7.operations;

import stmbench7.OperationId;
import stmbench7.Setup;
import stmbench7.ThreadRandom;
import stmbench7.annotations.ReadOnly;
import stmbench7.annotations.Transactional;
import stmbench7.backend.ImmutableCollection;
import stmbench7.backend.LargeSet;
import stmbench7.core.Assembly;
import stmbench7.core.AtomicPart;
import stmbench7.core.BaseAssembly;
import stmbench7.core.ComplexAssembly;
import stmbench7.core.CompositePart;
import stmbench7.core.Module;
import stmbench7.core.OperationFailedException;
import stmbench7.core.RuntimeError;

/**
 * Short traversal ST1 (see the specification).
 * Read-only, short.
 */
public class ShortTraversal1 extends BaseOperation {

	protected Module module;
	
	public ShortTraversal1(Setup oo7setup) {
		this.module = oo7setup.getModule();
	}

	@Override
	@Transactional @ReadOnly
	public int performOperation() throws OperationFailedException {
		ComplexAssembly designRoot = module.getDesignRoot();
		return traverse(designRoot);
	}

	protected int traverse(Assembly assembly) throws OperationFailedException {
		if(assembly instanceof ComplexAssembly) return traverse((ComplexAssembly)assembly);
		else return traverse((BaseAssembly)assembly);
	}
	
	protected int traverse(ComplexAssembly complexAssembly) throws OperationFailedException {
		ImmutableCollection<Assembly> subAssemblies = complexAssembly.getSubAssemblies();
		int numOfSubAssemblies = subAssemblies.size();
		int nextAssembly = ThreadRandom.nextInt(numOfSubAssemblies);
		
		int subAssemblyNumber = 0;
		for(Assembly subAssembly : subAssemblies) {
			if(subAssemblyNumber == nextAssembly) return traverse(subAssembly);
			subAssemblyNumber++;
		}
		
		throw new RuntimeError("ST1: size of ComplexAssemby.subAssemblies has changed!");
	}
	
	protected int traverse(BaseAssembly baseAssembly) throws OperationFailedException {
		ImmutableCollection<CompositePart> components = baseAssembly.getComponents();
		int numOfComponents = components.size();
		if(numOfComponents == 0) throw new OperationFailedException();
		
		int nextComponent = ThreadRandom.nextInt(numOfComponents);
		
		int componentNumber = 0;
		for(CompositePart component : components) {
			if(componentNumber == nextComponent) return traverse(component);
			componentNumber++;
		}
		
		throw new RuntimeError("ST1: size of BaseAssembly.components has changed!");
	}
	
	protected int traverse(CompositePart component) {
		LargeSet<AtomicPart> atomicParts = component.getParts();
		int numOfAtomicParts = atomicParts.size();
		int nextAtomicPart = ThreadRandom.nextInt(numOfAtomicParts);
		
		int atomicPartNumber = 0;
		for(AtomicPart atomicPart : atomicParts) {
			if(atomicPartNumber == nextAtomicPart) return traverse(atomicPart);
			atomicPartNumber++;
		}
		
		throw new RuntimeError("ST1: illegal size of CompositePart.parts!");
	}
	
	protected int traverse(AtomicPart atomicPart) {
		return atomicPart.getX() + atomicPart.getY();
	}
	
    @Override
    public OperationId getOperationId() {
    	return OperationId.ST1;
    }
}
