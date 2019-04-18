package stmbench7.impl.core;

import stmbench7.core.Assembly;
import stmbench7.core.ComplexAssembly;
import stmbench7.core.Module;


/**
 * STMBench7 benchmark Assembly (see the specification).
 * Default implementation.
 */
public abstract class AssemblyImpl extends DesignObjImpl implements Assembly {

    protected ComplexAssembly superAssembly;
    protected Module module;
    
    public AssemblyImpl(int id, String type, int buildDate, Module module, ComplexAssembly superAssembly) {
    	super(id, type, buildDate);
    	this.module = module;
    	this.superAssembly = superAssembly;
    }

    public AssemblyImpl(AssemblyImpl source) {
    	super(source);
    	this.superAssembly = source.superAssembly;
    	this.module = source.module;
    }
    
    public ComplexAssembly getSuperAssembly() {
    	return superAssembly;
    }
    
    public Module getModule() {
    	return module;
    }
    
    public void clearPointers() {
    	superAssembly = null;
    	module = null;
    }

	@Override
	public boolean equals(Object obj) {
		if(! (obj instanceof Assembly)) return false;
		return super.equals(obj);
	}
	
	@Override
	public String toString() {
		return super.toString() + ", superAssembly=[" + superAssembly + "]";
	}
}
