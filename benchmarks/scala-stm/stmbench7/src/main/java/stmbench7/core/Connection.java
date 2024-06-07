package stmbench7.core;

import stmbench7.annotations.Immutable;

/**
 * Part of the main benchmark data structure. For a default
 * implementation, see stmbench7.impl.core.ConnectionImpl.
 */
@Immutable
public interface Connection {

	Connection getReversed();
	AtomicPart getDestination();
	AtomicPart getSource();
	String getType();
	int getLength();
}
