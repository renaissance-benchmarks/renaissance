package stmbench7.impl.core;

import stmbench7.core.DesignObj;
import stmbench7.core.RuntimeError;

/**
 * STMBench7 benchmark Design Object (see the specification). Default
 * implementation.
 */
public class DesignObjImpl implements DesignObj, Cloneable {

	protected final int id;
	protected final String type;
	protected int buildDate;

	public DesignObjImpl(int id, String type, int buildDate) {
		this.id = id;
		this.type = type;
		this.buildDate = buildDate;
	}

	public DesignObjImpl(DesignObjImpl source) {
		this.id = source.id;
		this.type = source.type;
		this.buildDate = source.buildDate;
	}

	public int getId() {
		return id;
	}

	public int getBuildDate() {
		return buildDate;
	}

	public void updateBuildDate() {
		if (buildDate % 2 == 0)
			buildDate--;
		else
			buildDate++;
	}

	public void nullOperation() {
	}

	public String getType() {
		return type;
	}
	
	@Override
	public boolean equals(Object obj) {
		if(! (obj instanceof DesignObj)) return false;
		return ((DesignObj) obj).getId() == id;
	}
	
	@Override
	public int hashCode() {
		return id;
	}

	@Override
	public Object clone() {
		try {
			return super.clone();
		}
		catch(CloneNotSupportedException e) {
			throw new RuntimeError(e);
		}
	}
	
	@Override
	public String toString() {
		return this.getClass().getName() + 
			": id=" + id +
			", type=" + type +
			", buildDate=" + buildDate; 
	}
	
	protected String sequenceToString(Iterable<?> sequence) {
		String seqString = "{ ";
		for(Object element : sequence) seqString += element + " ";
		seqString += "}";
		return seqString;
	}
}
