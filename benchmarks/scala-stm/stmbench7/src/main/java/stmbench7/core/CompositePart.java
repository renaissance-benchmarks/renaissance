package stmbench7.core;

import stmbench7.annotations.Atomic;
import stmbench7.annotations.ReadOnly;
import stmbench7.annotations.Update;
import stmbench7.backend.ImmutableCollection;
import stmbench7.backend.LargeSet;

/**
 * Part of the main benchmark data structure. For a default
 * implementation, see stmbench7.impl.core.CompositePartImpl.
 */
@Atomic
public interface CompositePart extends DesignObj {

	@Update
	void addAssembly(BaseAssembly assembly);

	@Update
	boolean addPart(AtomicPart part);

	@Update
	void setRootPart(AtomicPart part);
	
	@ReadOnly
	AtomicPart getRootPart();

	@ReadOnly
	Document getDocumentation();

	@ReadOnly
	LargeSet<AtomicPart> getParts();

	@Update
	void removeAssembly(BaseAssembly assembly);

	@ReadOnly
	ImmutableCollection<BaseAssembly> getUsedIn();

	@Update
	void clearPointers();
}