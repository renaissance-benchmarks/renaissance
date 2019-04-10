package stmbench7.operations;

import stmbench7.OperationId;
import stmbench7.Parameters;
import stmbench7.Setup;
import stmbench7.ThreadRandom;
import stmbench7.annotations.ReadOnly;
import stmbench7.annotations.Transactional;
import stmbench7.backend.Index;
import stmbench7.core.BaseAssembly;
import stmbench7.core.Document;
import stmbench7.core.OperationFailedException;

/**
 * Query Q4 / Short traversal ST4 (see the specification).
 * Read-only, search on index, short.
 */
public class Query4 extends BaseOperation {

    Index<String,Document> documentTitleIndex;

    public Query4(Setup oo7setup) {
    	this.documentTitleIndex = oo7setup.getDocumentTitleIndex();
    }

    @Override
	@Transactional @ReadOnly
    public int performOperation() throws OperationFailedException {
    	int result = 0;

    	for(int i = 0; i < 100; i++) {
    		int partId = ThreadRandom.nextInt(Parameters.MaxCompParts) + 1;
    		String docTitle = "Composite Part #" + partId;

    		Document document = documentTitleIndex.get(docTitle);
    		if(document == null) continue;

    		for(BaseAssembly assembly : document.getCompositePart().getUsedIn()) {
    			assembly.nullOperation();
    			result++;
    		}
    	}

    	return result;
    }
    
    @Override
    public OperationId getOperationId() {
    	return OperationId.ST4;
    }
}

