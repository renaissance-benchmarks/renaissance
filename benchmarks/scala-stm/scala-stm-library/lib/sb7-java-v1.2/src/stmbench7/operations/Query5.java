package stmbench7.operations;

import stmbench7.OperationId;
import stmbench7.Setup;
import stmbench7.annotations.ReadOnly;
import stmbench7.annotations.Transactional;
import stmbench7.backend.Index;
import stmbench7.core.BaseAssembly;
import stmbench7.core.CompositePart;

/**
 * Query Q5 / Short traversal ST5 (see the specification).
 * Read-only, iterate on index, short.
 */
public class Query5 extends BaseOperation {

    protected Index<Integer,BaseAssembly> baseAssemblyIdIndex;

    public Query5(Setup oo7setup) {
    	this.baseAssemblyIdIndex = oo7setup.getBaseAssemblyIdIndex();
    }
	
    @Override
    @Transactional @ReadOnly
    public int performOperation() {
    	int result = 0;

    	for(BaseAssembly assembly : baseAssemblyIdIndex) {
    		result += checkBaseAssembly(assembly);
    	}
    		
    	return result;
    }

    protected int checkBaseAssembly(BaseAssembly assembly) {
    	int assBuildDate = assembly.getBuildDate();

    	for(CompositePart part : assembly.getComponents()) {
    		if(part.getBuildDate() > assBuildDate) {
    			assembly.nullOperation();
    			return 1;
    		}
    	}

    	return 0;
    }
    
    @Override
    public OperationId getOperationId() {
    	return OperationId.ST5;
    }
}
