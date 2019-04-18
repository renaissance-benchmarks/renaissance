package stmbench7.impl.core;

import stmbench7.backend.BackendFactory;
import stmbench7.backend.ImmutableCollection;
import stmbench7.backend.LargeSet;
import stmbench7.core.AtomicPart;
import stmbench7.core.BaseAssembly;
import stmbench7.core.CompositePart;
import stmbench7.core.Document;
import stmbench7.impl.backend.BagImpl;

/**
 * STMBench7 benchmark Composite Part (see the specification).
 */
public class CompositePartImpl extends DesignObjImpl implements CompositePart {

    private Document documentation;
    private BagImpl<BaseAssembly> usedIn;
    private LargeSet<AtomicPart> parts;
    private AtomicPart rootPart;

    public CompositePartImpl(int id, String type, int buildDate, Document documentation) {
    	super(id, type, buildDate);
    	this.documentation = documentation;
    	documentation.setPart(this);
    	usedIn = new BagImpl<BaseAssembly>();
    	parts = BackendFactory.instance.createLargeSet();
    }

    public CompositePartImpl(CompositePartImpl source) {
    	super(source);
    	this.documentation = source.documentation;
    	this.usedIn = new BagImpl<BaseAssembly>(source.usedIn);
    	this.parts = source.parts;
    	this.rootPart = source.rootPart;
    }
    
    public void addAssembly(BaseAssembly assembly) {
    	usedIn.add(assembly);
    }

    public boolean addPart(AtomicPart part) {
    	boolean notAddedBefore = parts.add(part);
    	if(! notAddedBefore) return false;

    	part.setCompositePart(this);
    	if(rootPart == null) rootPart = part;

    	return true;
    }

    public AtomicPart getRootPart() {
    	return rootPart;
    }

	public void setRootPart(AtomicPart part) {
		rootPart = part;
	}
	
    public Document getDocumentation() {
    	return documentation;
    }

    public LargeSet<AtomicPart> getParts() {
    	return parts;
    }

    public void removeAssembly(BaseAssembly assembly) {
    	usedIn.remove(assembly);
    }

    public ImmutableCollection<BaseAssembly> getUsedIn() {
    	return usedIn.immutableView();
    }
    
    public void clearPointers() {
    	documentation = null;
    	parts = null;
    	usedIn = null;
    	rootPart = null;
    }
    
	@Override
	public boolean equals(Object obj) {
		if(! (obj instanceof CompositePart)) return false;
		return super.equals(obj);
	}

    @SuppressWarnings("unchecked")
	@Override
	public Object clone() {
		CompositePartImpl clone = (CompositePartImpl) super.clone();
		clone.usedIn = (BagImpl<BaseAssembly>) usedIn.clone();
		return clone;
    }
}
