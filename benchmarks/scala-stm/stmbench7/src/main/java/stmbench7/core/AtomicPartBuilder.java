package stmbench7.core;

import stmbench7.Parameters;
import stmbench7.ThreadRandom;
import stmbench7.annotations.Immutable;
import stmbench7.backend.BackendFactory;
import stmbench7.backend.IdPool;
import stmbench7.backend.Index;
import stmbench7.backend.LargeSet;
import stmbench7.operations.BaseOperation;

/**
 * Used to create and destroy atomic parts while
 * maintaining the consistency of the data structure
 * and the indexes.
 */
@Immutable
public class AtomicPartBuilder extends DesignObjBuilder {

	private final IdPool idPool;

	private final Index<Integer,AtomicPart> partIdIndex;
	private final Index<Integer,LargeSet<AtomicPart>> partBuildDateIndex;

	public AtomicPartBuilder(Index<Integer,AtomicPart> partIdIndex,
			Index<Integer,LargeSet<AtomicPart>> partBuildDateIndex) {
		
		this.partIdIndex = partIdIndex;
		this.partBuildDateIndex = partBuildDateIndex;
		idPool = BackendFactory.instance.createIdPool(Parameters.MaxAtomicParts);
	}
	
	public AtomicPart createAndRegisterAtomicPart() throws OperationFailedException{
		int id = idPool.getId();
		String type = createType();
		int buildDate = createBuildDate(Parameters.MinAtomicDate, Parameters.MaxAtomicDate);
		int x = ThreadRandom.nextInt(Parameters.XYRange), 
			y = x + 1; // convenient for invariant tests
		
		AtomicPart part = designObjFactory.createAtomicPart(id, type, buildDate, x, y);

		partIdIndex.put(id, part);
		BaseOperation.addAtomicPartToBuildDateIndex(partBuildDateIndex, part);
	
		return part;
	}
	
	public void unregisterAndRecycleAtomicPart(AtomicPart part) {
		int partId = part.getId();

		BaseOperation.removeAtomicPartFromBuildDateIndex(partBuildDateIndex, part);
		partIdIndex.remove(partId);
		part.clearPointers();
		
		idPool.putUnusedId(partId);
	}
}
