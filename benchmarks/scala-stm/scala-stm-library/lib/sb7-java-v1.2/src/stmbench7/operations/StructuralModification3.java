package stmbench7.operations;

import stmbench7.OperationId;
import stmbench7.Parameters;
import stmbench7.Setup;
import stmbench7.ThreadRandom;
import stmbench7.annotations.Transactional;
import stmbench7.annotations.Update;
import stmbench7.backend.Index;
import stmbench7.core.BaseAssembly;
import stmbench7.core.CompositePart;
import stmbench7.core.OperationFailedException;

/**
 * Structural modification operation SM3 (see the specification).
 */
public class StructuralModification3 extends BaseOperation {

	protected Index<Integer,BaseAssembly> baseAssemblyIdIndex;
	protected Index<Integer,CompositePart> compositePartIdIndex;
	
	public StructuralModification3(Setup oo7setup) {
	
		this.baseAssemblyIdIndex = oo7setup.getBaseAssemblyIdIndex();
		this.compositePartIdIndex = oo7setup.getCompositePartIdIndex();
	}
	
	@Override
	@Transactional @Update
	public int performOperation() throws OperationFailedException {
		int baseAssemblyId = ThreadRandom.nextInt(Parameters.MaxBaseAssemblies) + 1;
		int componentId = ThreadRandom.nextInt(Parameters.MaxCompParts) + 1;
		BaseAssembly baseAssembly = baseAssemblyIdIndex.get(baseAssemblyId);
		CompositePart component = compositePartIdIndex.get(componentId);
		
		if(baseAssembly == null || component == null) throw new OperationFailedException();
		
		baseAssembly.addComponent(component);
		
		return 0;
	}
	
    @Override
    public OperationId getOperationId() {
    	return OperationId.SM3;
    }
}
