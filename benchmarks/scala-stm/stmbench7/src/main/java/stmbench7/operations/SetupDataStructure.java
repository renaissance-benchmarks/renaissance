package stmbench7.operations;

import stmbench7.OperationId;
import stmbench7.Parameters;
import stmbench7.Setup;
import stmbench7.ThreadRandom;
import stmbench7.annotations.Update;
import stmbench7.core.BaseAssembly;
import stmbench7.core.CompositePart;
import stmbench7.core.CompositePartBuilder;
import stmbench7.core.Module;
import stmbench7.core.Operation;
import stmbench7.core.OperationFailedException;
import stmbench7.core.RuntimeError;

/**
 * An operation that initializes the benchmark data structure.
 */
public class SetupDataStructure implements Operation {

	private final Setup setup;
	private Module module;
	
	public SetupDataStructure(Setup setup) {
		this.setup = setup;
	}
	
	@Update
	public int performOperation() throws OperationFailedException {
    	System.err.println("Setting up the design library:");
    	CompositePart designLibrary[] = new CompositePart[Parameters.InitialTotalCompParts];
    	CompositePartBuilder compositePartBuilder = setup.getCompositePartBuilder();
    	
    	for(int i = 0; i < Parameters.InitialTotalCompParts; i++) {
    	    System.err.print("Component " + (i+1) + " of " + Parameters.InitialTotalCompParts + "\r");
    	    try {
    	    	designLibrary[i] = compositePartBuilder.createAndRegisterCompositePart();
    	    }
    	    catch(OperationFailedException e) {
    	    	throw new RuntimeError("Unexpected failure of createAndRegisterCompositePart!", e);
    	    }
    	}
    	System.err.println();

    	System.err.println("Setting up the module:");
    	try {
    		module = setup.getModuleBuilder().createRegisterModule();
    	}
    	catch(OperationFailedException e) {
    		throw new RuntimeError("Unexpected failure of createRegisterModule!", e);
    	}
    	
    	int i = 1;
    	for(BaseAssembly baseAssembly : setup.getBaseAssemblyIdIndex()) {
    		System.err.print("Base Assembly " + (i++) + " of " + Parameters.InitialTotalBaseAssemblies + "\r");
    		
    		for(int connections = 0; connections < Parameters.NumCompPerAssm; connections++) {
    			int compositePartNum = ThreadRandom.nextInt(designLibrary.length);
    			baseAssembly.addComponent(designLibrary[compositePartNum]);
    		}
    	}
    	System.err.println();
    	
    	return 0;
	}

	public OperationId getOperationId() {
		return null;
	}
	
	public Module getModule() {
		return module;
	}
}
