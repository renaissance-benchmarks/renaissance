package stmbench7.impl.core;

import stmbench7.core.ComplexAssembly;
import stmbench7.core.Manual;
import stmbench7.core.Module;


/**
 * STMBench7 benchmark Module (see the specification).
 * Default implementation.
 */
public class ModuleImpl extends DesignObjImpl implements Module {

    private final Manual man;
    private ComplexAssembly designRoot;

    public ModuleImpl(int id, String type, int buildDate, Manual man) {
    	super(id, type, buildDate);
    	this.man = man;
    	man.setModule(this);
    }

    public ModuleImpl(ModuleImpl source) {
    	super(source);
    	this.man = source.man;
    	this.designRoot = source.designRoot;
    }
    
    public void setDesignRoot(ComplexAssembly designRoot) {
    	this.designRoot = designRoot;
    }
    
    public ComplexAssembly getDesignRoot() {
    	return designRoot;
    }

    public Manual getManual() {
    	return man;
    }
    
	@Override
	public boolean equals(Object obj) {
		if(! (obj instanceof Module)) return false;
		return super.equals(obj);
	}
}
