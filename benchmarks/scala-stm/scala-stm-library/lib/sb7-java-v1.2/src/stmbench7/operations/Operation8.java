package stmbench7.operations;

import stmbench7.OperationId;
import stmbench7.Parameters;
import stmbench7.Setup;
import stmbench7.ThreadRandom;
import stmbench7.annotations.ReadOnly;
import stmbench7.annotations.Transactional;
import stmbench7.backend.Index;
import stmbench7.core.BaseAssembly;
import stmbench7.core.CompositePart;
import stmbench7.core.OperationFailedException;

/**
 * Operation OP8 (see the specification).
 * Read-only, search on index.
 */
public class Operation8 extends BaseOperation {
	
	protected Index<Integer,BaseAssembly> baseAssemblyIdIndex;
	
	public Operation8(Setup oo7setup) {
		this.baseAssemblyIdIndex = oo7setup.getBaseAssemblyIdIndex();
	}
	
	@Override
	@Transactional @ReadOnly
	public int performOperation() throws OperationFailedException {
		int baseAssemblyId = ThreadRandom.nextInt(Parameters.MaxBaseAssemblies) +1;
		BaseAssembly baseAssembly = baseAssemblyIdIndex.get(baseAssemblyId);
		if(baseAssembly == null) throw new OperationFailedException();
		
		int count = 0;
		for(CompositePart component : baseAssembly.getComponents()) {
			performOperationInComponent(component);
			count++;
		}
		
		return count;
	}
	
	protected void performOperationInComponent(CompositePart component) {
		component.nullOperation();
	}
	
    @Override
    public OperationId getOperationId() {
    	return OperationId.OP8;
    }
}
