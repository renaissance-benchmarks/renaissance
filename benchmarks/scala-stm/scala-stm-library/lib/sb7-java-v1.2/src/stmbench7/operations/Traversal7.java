package stmbench7.operations;

import java.util.HashSet;

import stmbench7.OperationId;
import stmbench7.Parameters;
import stmbench7.Setup;
import stmbench7.ThreadRandom;
import stmbench7.annotations.ReadOnly;
import stmbench7.annotations.Transactional;
import stmbench7.backend.Index;
import stmbench7.core.Assembly;
import stmbench7.core.AtomicPart;
import stmbench7.core.BaseAssembly;
import stmbench7.core.CompositePart;
import stmbench7.core.OperationFailedException;

/**
 * Traversal T7 / Short traversal ST3 (see the specification).
 * Read-only, search on index, short.
 */
public class Traversal7 extends BaseOperation {

    Index<Integer,AtomicPart> partIdIndex;

    public Traversal7(Setup oo7setup) {
    	this.partIdIndex = oo7setup.getAtomicPartIdIndex();
    }

    @Override
    @Transactional @ReadOnly
    public int performOperation() throws OperationFailedException {
    	int partId = ThreadRandom.nextInt(Parameters.MaxAtomicParts) + 1;
    	AtomicPart part = partIdIndex.get(partId);
    	if(part == null) throw new OperationFailedException();
    	
    	return traverse(part.getPartOf());
    }

    protected int traverse(CompositePart part) {
    	HashSet<Assembly> visitedAssemblies = new HashSet<Assembly>();

    	int result = 0;
    	Iterable<BaseAssembly> ownerBaseAssemblies = part.getUsedIn();
    	for(BaseAssembly assembly : ownerBaseAssemblies)
    		result += traverse(assembly, visitedAssemblies);

    	return result;
    }

    protected int traverse(Assembly assembly, HashSet<Assembly> visitedAssemblies) {
    	if(assembly == null) return 0;
    	if(visitedAssemblies.contains(assembly)) return 0;

    	visitedAssemblies.add(assembly);

    	performOperationOnAssembly(assembly);
    	
    	return traverse(assembly.getSuperAssembly(), visitedAssemblies) + 1;
    }
    
    protected void performOperationOnAssembly(Assembly assembly) {
    	assembly.nullOperation();
    }
    
    @Override
    public OperationId getOperationId() {
    	return OperationId.ST3;
    }
}
