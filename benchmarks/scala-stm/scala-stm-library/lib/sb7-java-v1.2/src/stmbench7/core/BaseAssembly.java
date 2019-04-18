package stmbench7.core;

import stmbench7.annotations.Atomic;
import stmbench7.annotations.ReadOnly;
import stmbench7.annotations.Update;
import stmbench7.backend.ImmutableCollection;

/**
 * Part of the main benchmark data structure. For a default
 * implementation, see stmbench7.impl.core.BaseAssemblyImpl.
 */
@Atomic
public interface BaseAssembly extends Assembly {

	@Update
	void addComponent(CompositePart component);

	@Update
	boolean removeComponent(CompositePart component);

	@ReadOnly
	ImmutableCollection<CompositePart> getComponents();
}