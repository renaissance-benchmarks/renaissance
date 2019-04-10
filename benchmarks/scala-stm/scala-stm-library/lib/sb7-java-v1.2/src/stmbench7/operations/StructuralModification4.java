package stmbench7.operations;

import stmbench7.OperationId;
import stmbench7.Parameters;
import stmbench7.Setup;
import stmbench7.ThreadRandom;
import stmbench7.annotations.Transactional;
import stmbench7.annotations.Update;
import stmbench7.backend.ImmutableCollection;
import stmbench7.backend.Index;
import stmbench7.core.BaseAssembly;
import stmbench7.core.CompositePart;
import stmbench7.core.OperationFailedException;
import stmbench7.core.RuntimeError;

/**
 * Structural modification operation SM4 (see the specification).
 */
public class StructuralModification4 extends BaseOperation {

	protected Index<Integer,BaseAssembly> baseAssemblyIdIndex;
	
	public StructuralModification4(Setup oo7setup) {
		this.baseAssemblyIdIndex = oo7setup.getBaseAssemblyIdIndex();
	}
	
	@Override
	@Transactional @Update
	public int performOperation() throws OperationFailedException {
		int baseAssemblyId = ThreadRandom.nextInt(Parameters.MaxBaseAssemblies) + 1;
		BaseAssembly baseAssembly = baseAssemblyIdIndex.get(baseAssemblyId);
		if(baseAssembly == null) throw new OperationFailedException();
		
		ImmutableCollection<CompositePart> components = baseAssembly.getComponents();
		int numOfComponents = components.size();
		if(numOfComponents == 0) throw new OperationFailedException();
		
		int componentToRemove = ThreadRandom.nextInt(numOfComponents);
		
		int componentNumber = 0;
		for(CompositePart component : components) {
			if(componentNumber == componentToRemove) {
				baseAssembly.removeComponent(component);
				return 0;
			}
			componentNumber++;
		}
		
		throw new RuntimeError("SM4: concurrent modification of BaseAssembly.components!");
	}
	
    @Override
    public OperationId getOperationId() {
    	return OperationId.SM4;
    }
}