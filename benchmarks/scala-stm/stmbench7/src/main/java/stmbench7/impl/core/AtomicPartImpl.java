package stmbench7.impl.core;

import stmbench7.backend.ImmutableCollection;
import stmbench7.core.AtomicPart;
import stmbench7.core.CompositePart;
import stmbench7.core.Connection;
import stmbench7.impl.backend.SmallSetImpl;

/**
 * STMBench7 benchmark Atomic Part (see the specification).
 * Default implementation.
 */
public class AtomicPartImpl extends DesignObjImpl implements AtomicPart {

    private int x, y;
    protected SmallSetImpl<Connection> to, from;
    private CompositePart partOf;

    public AtomicPartImpl(int id, String type, int buildDate, int x, int y) {
    	super(id, type, buildDate);
    	this.x = x;
    	this.y = y;
    	to = new SmallSetImpl<Connection>();
    	from = new SmallSetImpl<Connection>();
    }

    public AtomicPartImpl(AtomicPartImpl source) {
    	super(source);
    	this.x = source.x;
    	this.y = source.y;
    	this.to = new SmallSetImpl<Connection>(source.to);
    	this.from = new SmallSetImpl<Connection>(source.from);
    	this.partOf = source.partOf;
    }
    
    public void connectTo(AtomicPart destination, String type, int length) {
    	Connection connection = new ConnectionImpl(this, destination, type, length);
    	to.add(connection);
    	destination.addConnectionFromOtherPart(connection.getReversed());
    }

    public void addConnectionFromOtherPart(Connection connection) {
    	from.add(connection);
    }
    
    public void setCompositePart(CompositePart partOf) {
    	this.partOf = partOf;
    }

    public int getNumToConnections() {
    	return to.size();
    }

    public ImmutableCollection<Connection> getToConnections() {
    	return to.immutableView();
    }

    public ImmutableCollection<Connection> getFromConnections() {
    	return from.immutableView();
    }
    
    public CompositePart getPartOf() {
    	return partOf;
    }

    public void swapXY() {
    	int tmp = y;
    	y = x;
    	x = tmp;
    }
    
    public int getX() {
    	return x;
    }
    
    public int getY() {
    	return y;
    }
    
    public void clearPointers() {
    	x = y = 0;
    	to = null;
    	from = null;
    	partOf = null;
    }

	public int compareTo(AtomicPart part) {
		return id - part.getId();
	}
	
	@Override
	public boolean equals(Object obj) {
		if(! (obj instanceof AtomicPart)) return false;
		return super.equals(obj);
	}

	@SuppressWarnings("unchecked")
	@Override
	public AtomicPartImpl clone() {
		AtomicPartImpl clone = (AtomicPartImpl) super.clone();
		clone.from = (SmallSetImpl<Connection>) from.clone();
		clone.to = (SmallSetImpl<Connection>) to.clone();
		return clone;
	}
	
	@Override
	public String toString() {
		return super.toString() + ", x=" + x + ", y=" + y + ", partOf=[" + partOf + "]" +
			", to={ " + to.size() + " connections }, from={ " + from.size() + " connections }"; 
	}
}
