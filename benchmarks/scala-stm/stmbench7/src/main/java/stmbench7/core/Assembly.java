package stmbench7.core;

import stmbench7.annotations.Atomic;
import stmbench7.annotations.ReadOnly;
import stmbench7.annotations.Update;

/**
 * Part of the main benchmark data structure. For a default
 * implementation, see stmbench7.impl.core.AssemblyImpl.
 */
@Atomic
public interface Assembly extends DesignObj {

	@ReadOnly
	ComplexAssembly getSuperAssembly();

	@ReadOnly
	Module getModule();

	@Update
	void clearPointers();
}