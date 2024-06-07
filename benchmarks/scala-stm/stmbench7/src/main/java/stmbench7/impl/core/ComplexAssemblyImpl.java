package stmbench7.impl.core;

import stmbench7.Parameters;
import stmbench7.backend.ImmutableCollection;
import stmbench7.core.Assembly;
import stmbench7.core.BaseAssembly;
import stmbench7.core.ComplexAssembly;
import stmbench7.core.Module;
import stmbench7.core.RuntimeError;
import stmbench7.impl.backend.SmallSetImpl;

/**
 * STMBench7 benchmark Complex Assembly (see the specification).
 * Default implementation.
 */
public class ComplexAssemblyImpl extends AssemblyImpl implements ComplexAssembly {

    private SmallSetImpl<Assembly> subAssemblies;
    private short level; 
    
    public ComplexAssemblyImpl(int id, String type, int buildDate, Module module, ComplexAssembly superAssembly) {
    	super(id, type, buildDate, module, superAssembly);
    	subAssemblies = new SmallSetImpl<Assembly>();
    	
       	if(superAssembly == null) level = Parameters.NumAssmLevels;
    	else level = (short)(superAssembly.getLevel() - 1);
    }

    public ComplexAssemblyImpl(ComplexAssemblyImpl source) {
    	super(source);
    	this.subAssemblies = new SmallSetImpl<Assembly>(subAssemblies);
    	this.level = source.level;
    }
    
    public boolean addSubAssembly(Assembly assembly) {
    	if(assembly instanceof BaseAssembly && level != 2)
    		throw new RuntimeError("ComplexAssembly.addAssembly: BaseAssembly at wrong level!");
    	
    	boolean notAddedBefore = subAssemblies.add(assembly);
    	return notAddedBefore;
    }

    public boolean removeSubAssembly(Assembly assembly) {
    	return subAssemblies.remove(assembly);
    }
    
    public ImmutableCollection<Assembly> getSubAssemblies() {
    	return subAssemblies.immutableView();
    }
    
    public short getLevel() {
    	return level;
    }
    
    @Override
    public void clearPointers() {
    	super.clearPointers();
    	subAssemblies = null;
    	level = -1;
    }
    
	@Override
	public boolean equals(Object obj) {
		if(! (obj instanceof ComplexAssembly)) return false;
		return super.equals(obj);
	}

    @SuppressWarnings("unchecked")
	@Override
	public ComplexAssemblyImpl clone() {
		ComplexAssemblyImpl clone = (ComplexAssemblyImpl) super.clone();
		clone.subAssemblies = (SmallSetImpl<Assembly>) subAssemblies.clone();
		return clone;
	}
    
    @Override
    public String toString() {
    	String subAssString = "{ ";
    	for(Assembly subAssembly : subAssemblies) 
    		subAssString += subAssembly.getId() + " ";
    	subAssString += "}";
    	return super.toString() + ", level=" + level + ", subAssemblies=" + subAssString;
    }
}
