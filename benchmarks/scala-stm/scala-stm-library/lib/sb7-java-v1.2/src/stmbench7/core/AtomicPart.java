package stmbench7.core;

import stmbench7.annotations.Atomic;
import stmbench7.annotations.ReadOnly;
import stmbench7.annotations.Update;
import stmbench7.backend.ImmutableCollection;

/**
 * Part of the main benchmark data structure. For a default
 * implementation, see stmbench7.impl.core.AtomicPartImpl.
 */
@Atomic
public interface AtomicPart extends DesignObj, Comparable<AtomicPart> {

	@Update
	void connectTo(AtomicPart destination, String type, int length);

	@Update
	void addConnectionFromOtherPart(Connection connection);
	
	@Update
	void setCompositePart(CompositePart partOf);

	@ReadOnly
	int getNumToConnections();

	@ReadOnly
	ImmutableCollection<Connection> getToConnections();

	@ReadOnly
	ImmutableCollection<Connection> getFromConnections();
	
	@ReadOnly
	CompositePart getPartOf();

	@Update
	void swapXY();

	@ReadOnly
	int getX();

	@ReadOnly
	int getY();

	@Update
	void clearPointers();
}
