package stmbench7.operations;

import stmbench7.OperationId;
import stmbench7.Setup;
import stmbench7.annotations.Transactional;
import stmbench7.annotations.Update;
import stmbench7.core.Document;
import stmbench7.core.RuntimeError;

/**
 * Traversal T5 (see the specification).
 */
public class Traversal5 extends Traversal4 {

    public Traversal5(Setup oo7setup) {
    	super(oo7setup);
    }

	@Override
	@Transactional @Update
	public int performOperation() {
    	return super.performOperation();
	}
	
    @Override
    protected int traverse(Document documentation) {
    	int result;
    	
    	if(documentation.textBeginsWith("I am"))
    		result = documentation.replaceText("I am", "This is");
    	else if(documentation.textBeginsWith("This is"))
    		result = documentation.replaceText("This is", "I am");
    	else
    		throw new RuntimeError("T5: illegal document text: " + documentation.getText());
    
    	if(result == 0) throw new RuntimeError("T5: concurrent modification!");
    	return result;
    }
    
    @Override
    public OperationId getOperationId() {
    	return OperationId.T5;
    }
}
