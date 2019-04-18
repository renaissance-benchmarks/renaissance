package stmbench7.operations;

import stmbench7.OperationId;
import stmbench7.Parameters;
import stmbench7.Setup;
import stmbench7.ThreadRandom;
import stmbench7.annotations.ReadOnly;
import stmbench7.annotations.Transactional;
import stmbench7.backend.Index;
import stmbench7.core.Assembly;
import stmbench7.core.BaseAssembly;
import stmbench7.core.ComplexAssembly;
import stmbench7.core.OperationFailedException;

/**
 * Operation OP7 (see the specification).
 * Read-only, search on index.
 */
public class Operation7 extends BaseOperation {

	protected Index<Integer,BaseAssembly> baseAssemblyIdIndex;
	
	public Operation7(Setup oo7setup) {
		this.baseAssemblyIdIndex = oo7setup.getBaseAssemblyIdIndex();
	}
	
	@Override
	@Transactional @ReadOnly
	public int performOperation() throws OperationFailedException {
		int baseAssemblyId = ThreadRandom.nextInt(Parameters.MaxBaseAssemblies) +1;
		BaseAssembly baseAssembly = baseAssemblyIdIndex.get(baseAssemblyId);
		if(baseAssembly == null) throw new OperationFailedException();
		
		ComplexAssembly superAssembly = baseAssembly.getSuperAssembly();
		
		int count = 0;
		for(Assembly siblingAssembly : superAssembly.getSubAssemblies()) {
			performOperationInBaseAssembly((BaseAssembly)siblingAssembly);
			count++;
		}
		
		return count;
	}
	
	protected void performOperationInBaseAssembly(BaseAssembly assembly) {
		assembly.nullOperation();
	}
	
    @Override
    public OperationId getOperationId() {
    	return OperationId.OP7;
    }
}
