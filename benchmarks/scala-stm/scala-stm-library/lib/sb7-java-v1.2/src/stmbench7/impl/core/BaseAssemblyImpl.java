package stmbench7.impl.core;

import stmbench7.backend.ImmutableCollection;
import stmbench7.core.BaseAssembly;
import stmbench7.core.ComplexAssembly;
import stmbench7.core.CompositePart;
import stmbench7.core.Module;
import stmbench7.impl.backend.BagImpl;

/**
 * STMBench7 benchmark Base Assembly (see the specification).
 * Default implementation.
 */
public class BaseAssemblyImpl extends AssemblyImpl implements BaseAssembly {

    protected BagImpl<CompositePart> components;

    public BaseAssemblyImpl(int id, String type, int buildDate, Module module, ComplexAssembly superAssembly) {
    	super(id, type, buildDate, module, superAssembly);
		components = new BagImpl<CompositePart>();
    }

    public BaseAssemblyImpl(BaseAssemblyImpl source) {
    	super(source);
    	this.components = new BagImpl<CompositePart>(source.components);
    }
    
    public void addComponent(CompositePart component) {
    	components.add(component);
    	component.addAssembly(this);
    }

    public boolean removeComponent(CompositePart component) {
    	boolean componentExists = components.remove(component);
    	if(! componentExists) return false;
    	
    	component.removeAssembly(this);
    	return true;
    }

    public ImmutableCollection<CompositePart> getComponents() {
    	return components.immutableView();
    }
    
    @Override
    public void clearPointers() {
    	super.clearPointers();
    	components = null;
    }

	@Override
	public boolean equals(Object obj) {
		if(! (obj instanceof BaseAssembly)) return false;
		return super.equals(obj);
	}

    @SuppressWarnings("unchecked")
	@Override
	public BaseAssemblyImpl clone() {
		BaseAssemblyImpl clone = (BaseAssemblyImpl) super.clone();
		clone.components = (BagImpl<CompositePart>) components.clone();
		return clone;
	}
    
    @Override
    public String toString() {
    	String componentIds = "{ ";
    	for(CompositePart component : components) componentIds += component.getId() + " ";
    	componentIds += "}";
    	return super.toString() + ", components=" + componentIds; 
    }
}
