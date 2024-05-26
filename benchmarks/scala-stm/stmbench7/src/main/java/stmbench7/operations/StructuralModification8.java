package stmbench7.operations;

import stmbench7.OperationId;
import stmbench7.Parameters;
import stmbench7.Setup;
import stmbench7.ThreadRandom;
import stmbench7.annotations.Transactional;
import stmbench7.annotations.Update;
import stmbench7.core.ComplexAssembly;
import stmbench7.core.OperationFailedException;

/**
 * Structural modification SM8 (see the specification).
 */
public class StructuralModification8 extends StructuralModification7 {

	public StructuralModification8(Setup oo7setup) {
		super(oo7setup);
	}

	@Override
	@Transactional @Update
	public int performOperation() throws OperationFailedException {
		int complexAssemblyId = ThreadRandom.nextInt(Parameters.MaxComplexAssemblies) + 1;
		ComplexAssembly complexAssembly = complexAssemblyIdIndex.get(complexAssemblyId);
		if(complexAssembly == null) throw new OperationFailedException();

		// We want the tree of BAs/CAs to keep its form 
		// so that each CA has always at least one child sub-assembly
		ComplexAssembly superAssembly = complexAssembly.getSuperAssembly();
		if(superAssembly == null || superAssembly.getSubAssemblies().size() == 1)
			throw new OperationFailedException();
		
		assemblyBuilder.unregisterAndRecycleComplexAssembly(complexAssembly);
		
		return 1;
	}
	
    @Override
    public OperationId getOperationId() {
    	return OperationId.SM8;
    }
}
