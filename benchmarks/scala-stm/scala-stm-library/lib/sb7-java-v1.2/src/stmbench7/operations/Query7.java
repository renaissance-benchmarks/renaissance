package stmbench7.operations;

import stmbench7.OperationId;
import stmbench7.Setup;
import stmbench7.annotations.ReadOnly;
import stmbench7.annotations.Transactional;
import stmbench7.backend.Index;
import stmbench7.core.AtomicPart;

/**
 * Query Q7 (see the specification).
 * Read-only, iterate on index, long.
 */
public class Query7 extends BaseOperation {

    protected Index<Integer,AtomicPart> partIdIndex;

    public Query7(Setup oo7setup) {
    	this.partIdIndex = oo7setup.getAtomicPartIdIndex();
    }

    @Override
    @Transactional @ReadOnly
    public int performOperation() {
    	int result = 0;
    	for(AtomicPart part : partIdIndex) {
    		part.nullOperation();
    		result++;
    	}
    	return result;
    }
    
    @Override
    public OperationId getOperationId() {
    	return OperationId.Q7;
    }
}
