package stmbench7.impl.backend;

import java.util.LinkedList;

import stmbench7.annotations.Update;
import stmbench7.backend.IdPool;
import stmbench7.core.OperationFailedException;

/**
 * Used to generate ids of various elements.
 * This default implementation is NOT thread-safe.
 */
public class IdPoolImpl implements IdPool, Cloneable {

    private final LinkedList<Integer> idPool;
    
    public IdPoolImpl(int maxNumberOfIds) {
    	idPool = new LinkedList<Integer>();
    	for(int id = 1; id <= maxNumberOfIds; id++) {
    		idPool.offer(id);
    	}
    }

    @Update
    public int getId() throws OperationFailedException {
    	Integer id = idPool.poll();
    	if(id == null) throw new OperationFailedException();
    	
    	return id;
    }
    
    @Update
    public void putUnusedId(int id) {
    	idPool.offer(id);
    }
    
    public String toString() {
    	String txt = "IdPool:";
    	for(int id : idPool) txt += " " + id;
    	return txt;
    }
    
    private IdPoolImpl(LinkedList<Integer> idPool) {
    	this.idPool = idPool;
    }
    
	@SuppressWarnings("unchecked")
	@Override
	public IdPoolImpl clone() {
		return new IdPoolImpl((LinkedList<Integer>) idPool.clone());
	}
}
