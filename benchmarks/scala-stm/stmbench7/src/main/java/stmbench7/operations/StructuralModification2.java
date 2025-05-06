package stmbench7.operations;

import stmbench7.OperationId;
import stmbench7.Parameters;
import stmbench7.Setup;
import stmbench7.ThreadRandom;
import stmbench7.annotations.Transactional;
import stmbench7.annotations.Update;
import stmbench7.backend.Index;
import stmbench7.core.CompositePart;
import stmbench7.core.OperationFailedException;

/**
 * Structural modification operation SM2 (see the specification).
 */
public class StructuralModification2 extends StructuralModification1 {

	protected Index<Integer, CompositePart> compositePartIdIndex;
	
	public StructuralModification2(Setup oo7setup) {

		super(oo7setup);
		this.compositePartIdIndex = oo7setup.getCompositePartIdIndex();
	}

	@Override
	@Transactional @Update
	public int performOperation() throws OperationFailedException {
		int partToRemoveId = ThreadRandom.nextInt(Parameters.MaxCompParts) + 1;
		CompositePart partToRemove = compositePartIdIndex.get(partToRemoveId);
		if(partToRemove == null) throw new OperationFailedException();
		
		compositePartBuilder.unregisterAndRecycleCompositePart(partToRemove);
		return 0;
	}
	
    @Override
    public OperationId getOperationId() {
    	return OperationId.SM2;
    }
}
