package stmbench7.core;

import stmbench7.annotations.Atomic;
import stmbench7.annotations.ReadOnly;
import stmbench7.annotations.Update;

/**
 * Root of the benchmark main data structure. For a default
 * implementation, see stmbench7.impl.core.ModuleImpl.
 */
@Atomic
public interface Module extends DesignObj {

	@Update
	void setDesignRoot(ComplexAssembly designRoot);

	@ReadOnly
	ComplexAssembly getDesignRoot();

	@ReadOnly
	Manual getManual();
}
