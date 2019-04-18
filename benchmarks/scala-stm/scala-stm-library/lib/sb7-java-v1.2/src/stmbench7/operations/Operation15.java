package stmbench7.operations;

import stmbench7.OperationId;
import stmbench7.Setup;
import stmbench7.annotations.Transactional;
import stmbench7.annotations.Update;
import stmbench7.backend.Index;
import stmbench7.backend.LargeSet;
import stmbench7.core.AtomicPart;
import stmbench7.core.OperationFailedException;

/**
 * Operation OP15 (see the specification).
 * Simple update, search and update on index.
 */
public class Operation15 extends Query1 {

	protected Index<Integer,LargeSet<AtomicPart>> partBuildDateIndex;
	
	public Operation15(Setup oo7setup) {
		super(oo7setup);
		this.partBuildDateIndex = oo7setup.getAtomicPartBuildDateIndex();
	}
	
    @Override
	@Transactional @Update
	public int performOperation() throws OperationFailedException {
    	return super.performOperation();
	}
    
    @Override
	protected void performOperationInAtomicPart(AtomicPart atomicPart) {
		removeAtomicPartFromBuildDateIndex(partBuildDateIndex, atomicPart);
		atomicPart.updateBuildDate();
		addAtomicPartToBuildDateIndex(partBuildDateIndex, atomicPart);
	}
    
    @Override
    public OperationId getOperationId() {
    	return OperationId.OP15;
    }
}
