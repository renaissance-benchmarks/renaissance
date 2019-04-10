package stmbench7.core;

import stmbench7.annotations.Atomic;
import stmbench7.annotations.ReadOnly;
import stmbench7.annotations.Update;
import stmbench7.backend.ImmutableCollection;

/**
 * Part of the main benchmark data structure. For a default
 * implementation, see stmbench7.impl.core.ComplexAssemblyImpl.
 */
@Atomic
public interface ComplexAssembly extends Assembly {

	@Update
	boolean addSubAssembly(Assembly assembly);

	@Update
	boolean removeSubAssembly(Assembly assembly);

	@ReadOnly
	ImmutableCollection<Assembly> getSubAssemblies();

	@ReadOnly
	short getLevel();
}