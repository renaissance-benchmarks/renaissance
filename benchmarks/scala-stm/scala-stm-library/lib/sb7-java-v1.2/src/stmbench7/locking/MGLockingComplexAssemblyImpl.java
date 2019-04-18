package stmbench7.locking;

import stmbench7.core.ComplexAssembly;
import stmbench7.core.Module;
import stmbench7.impl.core.ComplexAssemblyImpl;

/**
 * An implementation of the ComplexAssembly interface used in the
 * medium-grained locking synchronization method. The complex
 * assembly is locked for reading or writing by the methods that read
 * or modify the object (except for cases when the required
 * locking is done externally).
 */
public class MGLockingComplexAssemblyImpl extends ComplexAssemblyImpl {

	public MGLockingComplexAssemblyImpl(int id, String type, int buildDate,
			Module module, ComplexAssembly superAssembly) {
		super(id, type, buildDate, module, superAssembly);
	}

	/*
	 * Methods "add/removeSubAssembly", "getSubAssemblies" and "clearPointers"
	 * assume global structure lock is held when those are called. Attributes
	 * "level", "superAssembly" and "module" can also be changed only when the
	 * global structure lock is held in write mode.
	 */

	@Override
	public int getBuildDate() {
		MGLockingOperationExecutor.readLockAssemblyLevel(getLevel());
		return super.getBuildDate();
	}

	@Override
	public void updateBuildDate() {
		MGLockingOperationExecutor.writeLockAssemblyLevel(getLevel());
		super.updateBuildDate();
	}

	@Override
	public void nullOperation() {
		MGLockingOperationExecutor.readLockAssemblyLevel(getLevel());
	}

	@Override
	public String getType() {
		MGLockingOperationExecutor.readLockAssemblyLevel(getLevel());
		return super.getType();
	}
}
