package stmbench7.impl.core;

import stmbench7.core.AtomicPart;
import stmbench7.core.Connection;
import stmbench7.core.RuntimeError;


/**
 * STMBench7 benchmark Connection (see the specification).
 * Default implementation.
 */
public class ConnectionImpl implements Connection, Cloneable {

    protected final String type;
    protected final int length;
    protected final AtomicPart from, to;

    public ConnectionImpl(AtomicPart from, AtomicPart to, String type, int length) {
    	this.type = type;
    	this.length = length;
    	this.from = from;
    	this.to = to;
    }

    public Connection getReversed() {
    	return new ConnectionImpl(to, from, new String(type), length);
    }

	public AtomicPart getSource() {
		return from;
	}

    public AtomicPart getDestination() {
    	return to;
    }

	public int getLength() {
		return length;
	}

	public String getType() {
		return type;
	}
	
	public Object clone() {
		try {
			return super.clone();
		}
		catch(CloneNotSupportedException e) {
			throw new RuntimeError(e);
		}
	}
}
