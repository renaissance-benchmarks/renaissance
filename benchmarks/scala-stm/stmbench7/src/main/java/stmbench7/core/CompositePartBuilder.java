package stmbench7.core;

import stmbench7.Parameters;
import stmbench7.ThreadRandom;
import stmbench7.annotations.Immutable;
import stmbench7.backend.BackendFactory;
import stmbench7.backend.IdPool;
import stmbench7.backend.ImmutableCollection;
import stmbench7.backend.Index;
import stmbench7.backend.LargeSet;

/**
 * Used to create and destroy composite parts while
 * maintaining the consistency of the data structure
 * and the indexes.
 */
@Immutable
public class CompositePartBuilder extends DesignObjBuilder {

	private final IdPool idPool; 
	
	private final Index<Integer,CompositePart> compositePartIdIndex;
	private final DocumentBuilder documentBuilder;
	private final AtomicPartBuilder atomicPartBuilder;
	
	public CompositePartBuilder(Index<Integer,CompositePart> compositePartIdIndex,
			Index<String,Document> documentTitleIndex,
			Index<Integer,AtomicPart> partIdIndex,
			Index<Integer,LargeSet<AtomicPart>> partBuildDateIndex) {
		
		this.compositePartIdIndex = compositePartIdIndex;
		documentBuilder = new DocumentBuilder(documentTitleIndex);
		atomicPartBuilder = new AtomicPartBuilder(partIdIndex, partBuildDateIndex);
		idPool = BackendFactory.instance.createIdPool(Parameters.MaxCompParts);
	}
	
	/**
     * Creates a component (composite part) with the documentation and
     * a graph of atomic parts and updates all the relevant indexes.
     */
	public CompositePart createAndRegisterCompositePart() throws OperationFailedException {
		int id = idPool.getId();
		String type = createType();
			
		int buildDate;
		if(ThreadRandom.nextInt(100) < Parameters.YoungCompFrac)
		    buildDate = createBuildDate(Parameters.MinYoungCompDate, Parameters.MaxYoungCompDate);
		else
		    buildDate = createBuildDate(Parameters.MinOldCompDate, Parameters.MaxOldCompDate);

		Document documentation = null;
		AtomicPart parts[] = new AtomicPart[Parameters.NumAtomicPerComp];

		try {
			documentation = documentBuilder.createAndRegisterDocument(id);
			createAtomicParts(parts);
		}
		catch(OperationFailedException e) {
			if(documentation != null) documentBuilder.unregisterAndRecycleDocument(documentation);
			for(AtomicPart part : parts)
				if(part != null) atomicPartBuilder.unregisterAndRecycleAtomicPart(part);
			idPool.putUnusedId(id);
			throw e;
		}
		
		createConnections(parts);

		CompositePart component = designObjFactory.createCompositePart(id, type, buildDate, documentation);
	    for(AtomicPart part : parts) component.addPart(part);
	    
	    compositePartIdIndex.put(id, component);

	    return component;
	}

	public void unregisterAndRecycleCompositePart(CompositePart compositePart) {
		int id = compositePart.getId();
		compositePartIdIndex.remove(id);
		
		documentBuilder.unregisterAndRecycleDocument(compositePart.getDocumentation());
		
		for(AtomicPart atomicPart : compositePart.getParts())
			atomicPartBuilder.unregisterAndRecycleAtomicPart(atomicPart);
		
		ImmutableCollection<BaseAssembly> usedInList = compositePart.getUsedIn().clone();
		for(BaseAssembly ownerAssembly : usedInList) {
			while(ownerAssembly.removeComponent(compositePart));
		}
		
		compositePart.clearPointers();
		idPool.putUnusedId(id);
	}

	/**
	 * Create all atomic parts of a given composite part.
	 */ 
	private void createAtomicParts(AtomicPart[] parts) throws OperationFailedException {
		
		for(int partNum = 0; partNum < Parameters.NumAtomicPerComp; partNum++) {
		    AtomicPart part = atomicPartBuilder.createAndRegisterAtomicPart();
		    parts[partNum] = part;
		}
	}
	
	/**
	 * Create connections between the parts.
	 */
	private void createConnections(AtomicPart[] parts) {

    	// First, make all atomic parts be connected in a ring
    	// (so that the resulting graph is fully connected)
		for(int partNum = 0; partNum < Parameters.NumAtomicPerComp; partNum++) {
			int connectTo = (partNum + 1) % Parameters.NumAtomicPerComp;
			parts[partNum].connectTo(parts[connectTo], createType(), 
					ThreadRandom.nextInt(Parameters.XYRange) + 1);
		}
		
    	// Then add other connections randomly, taking into account
    	// the NumConnPerAtomic parameter. The procedure is non-deterministic
    	// but it should eventually terminate.
		for(int partNum = 0; partNum < Parameters.NumAtomicPerComp; partNum++) {
			AtomicPart currentPart = parts[partNum];
			
		    while(currentPart.getNumToConnections() < Parameters.NumConnPerAtomic) {
		    	int connectTo = ThreadRandom.nextInt(Parameters.NumAtomicPerComp);
		    	parts[partNum].connectTo(parts[connectTo], createType(), 
		    			ThreadRandom.nextInt(Parameters.XYRange) + 1);
		    }
		}
	}
}
