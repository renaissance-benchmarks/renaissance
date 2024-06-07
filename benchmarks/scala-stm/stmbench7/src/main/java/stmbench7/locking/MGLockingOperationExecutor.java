package stmbench7.locking;

import java.util.ArrayList;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantReadWriteLock;

import stmbench7.OperationExecutor;
import stmbench7.OperationId;
import stmbench7.OperationType;
import stmbench7.Parameters;
import stmbench7.core.Operation;
import stmbench7.core.OperationFailedException;
import stmbench7.core.RuntimeError;

/**
 * Implementation of the OperationExecutor used by the medium-grained
 * locking method. It implements externally most of the locking
 * for each operation. The locks for each operation are predefined,
 * except for some complex assembly locks that may be acquired
 * by some complex assembly methods (see the MGLockingComplexAssemblyImpl
 * class).
 * 
 * Locking order:
 * <ol>
 * <li> Global structure lock,
 * <li> Manual lock,
 * <li> Base assemblies lock,
 * <li> Composite parts lock,
 * <li> Documents lock,
 * <li> Atomic parts lock,
 * <li> Complex assemblies locks: starting from the highest level
 * 		(Parameters.NumAssmLevels), down to the lowest level
 * 		(BASE_ASSEMBLY_LEVEL + 1).
 * </ol>
 */
public class MGLockingOperationExecutor implements OperationExecutor {

	private static final int BASE_ASSEMBLY_LEVEL = 1;

	/**
	 * Global structure lock is acquired by every operation:
	 * <ol>
	 * <li> in write mode, if the operation modifies the data structure (i.e.,
	 * adds or removes some elements) or modifies one of the indexes; and
	 * <li> in read mode otherwise.
	 * </ol>
	 */
	private static final Lock globalStructureReadLock,
			globalStructureWriteLock;

	/**
	 * Per-assembly-level locks.
	 */
	private static final ReentrantReadWriteLock[] assemblyLocks;
	private static final Lock[] assemblyReadLocks, assemblyWriteLocks;

	/**
	 * Per-object-type locks.
	 */
	private static final Lock compositePartReadLock, compositePartWriteLock,
			atomicPartReadLock, atomicPartWriteLock, documentReadLock,
			documentWriteLock, manualReadLock, manualWriteLock;

	/**
	 * Used for generating timestamps for the replay log.
	 */
	private static final AtomicInteger globalCounter = new AtomicInteger();

	/**
	 * Determines which per-assembly-level locks were acquired by the
	 * MGLockingComplexAssemblyImpl class.
	 */
	private static class AssemblyLocksAcquired {
		public final boolean[] isReadAcquired, isWriteAcquired;

		public AssemblyLocksAcquired() {
			isReadAcquired = new boolean[Parameters.NumAssmLevels + 1];
			isWriteAcquired = new boolean[Parameters.NumAssmLevels + 1];
			clear();
		}

		public void clear() {
			for (int level = 0; level <= Parameters.NumAssmLevels; level++) {
				isReadAcquired[level] = false;
				isWriteAcquired[level] = false;
			}
		}
	}

	private static final ThreadLocal<AssemblyLocksAcquired> assemblyLocksAcquired = 
		new ThreadLocal<AssemblyLocksAcquired>() {
		@Override
		protected AssemblyLocksAcquired initialValue() {
			return new AssemblyLocksAcquired();
		}
	};

	static {
		ReentrantReadWriteLock globalStructureLock = new ReentrantReadWriteLock(
				false);
		globalStructureReadLock = globalStructureLock.readLock();
		globalStructureWriteLock = globalStructureLock.writeLock();

		assemblyLocks = new ReentrantReadWriteLock[Parameters.NumAssmLevels + 1];
		assemblyReadLocks = new Lock[Parameters.NumAssmLevels + 1];
		assemblyWriteLocks = new Lock[Parameters.NumAssmLevels + 1];
		for (int level = 1; level <= Parameters.NumAssmLevels; level++) {
			assemblyLocks[level] = new ReentrantReadWriteLock(false);
			assemblyReadLocks[level] = assemblyLocks[level].readLock();
			assemblyWriteLocks[level] = assemblyLocks[level].writeLock();
		}
		ReentrantReadWriteLock compositePartLock = new ReentrantReadWriteLock(
				false);
		compositePartReadLock = compositePartLock.readLock();
		compositePartWriteLock = compositePartLock.writeLock();

		ReentrantReadWriteLock atomicPartLock = new ReentrantReadWriteLock(
				false);
		atomicPartReadLock = atomicPartLock.readLock();
		atomicPartWriteLock = atomicPartLock.writeLock();

		ReentrantReadWriteLock documentLock = new ReentrantReadWriteLock(false);
		documentReadLock = documentLock.readLock();
		documentWriteLock = documentLock.writeLock();

		ReentrantReadWriteLock manualLock = new ReentrantReadWriteLock(false);
		manualReadLock = manualLock.readLock();
		manualWriteLock = manualLock.writeLock();
	}

	/**
	 * Called by a MGLockingComplexAssemblyImpl method to 
	 * read-lock a given complex assembly level.
	 */
	public static void readLockAssemblyLevel(int level) {
		AssemblyLocksAcquired threadAssemblyLocksAcquired = 
			assemblyLocksAcquired.get();
		if (threadAssemblyLocksAcquired.isReadAcquired[level]
				|| threadAssemblyLocksAcquired.isWriteAcquired[level])
			return;

		assemblyReadLocks[level].lock();
		threadAssemblyLocksAcquired.isReadAcquired[level] = true;
	}

	/**
	 * Called by a MGLockingComplexAssemblyImpl method to 
	 * write-lock a given complex assembly level.
	 */
	public static void writeLockAssemblyLevel(int level) {
		AssemblyLocksAcquired threadAssemblyLocksAcquired = 
			assemblyLocksAcquired.get();
		if (threadAssemblyLocksAcquired.isWriteAcquired[level])
			return;

		assemblyWriteLocks[level].lock();
		threadAssemblyLocksAcquired.isWriteAcquired[level] = true;
	}

	private final Operation op;
	private final ArrayList<Lock> locksToAcquire;
	private int lastOperationTimestamp;

	public MGLockingOperationExecutor(Operation op) {
		this.op = op;

		// Decide which locks should be acquired when a given
		// operation is executed
		locksToAcquire = new ArrayList<Lock>();
		OperationId operationId = op.getOperationId();
		if(operationId == null) return;
		OperationType operationType = operationId.getType();

		// Structural modification operations: exclusive access
		if (operationType == OperationType.STRUCTURAL_MODIFICATION) {
			locksToAcquire.add(globalStructureWriteLock);
			return;
		}
		
		// Other operations: assume the structure is not modified
		locksToAcquire.add(globalStructureReadLock);

		// Handling of individual cases
		switch (op.getOperationId()) {
		case T1:
		case T6:
		case Q7:
		case ST1:
		case ST9:
		case OP1:
		case OP2:
		case OP3:
			locksToAcquire.add(atomicPartReadLock);
			break;
		case T2a:
		case T2b:
		case T2c:
		case T3a:
		case T3b:
		case T3c:
		case ST6:
		case ST10:
		case OP9:
		case OP10:
		case OP15:
			locksToAcquire.add(atomicPartWriteLock);
			break;

		case T4:
		case ST2:
			locksToAcquire.add(documentReadLock);
			break;
		case T5:
		case ST7:
			locksToAcquire.add(documentWriteLock);
			break;

		case Q6:
			locksToAcquire.add(assemblyReadLocks[BASE_ASSEMBLY_LEVEL]);
			locksToAcquire.add(compositePartReadLock);
			// Pre-lock all assembly levels to avoid deadlocks
			for (int level = Parameters.NumAssmLevels; level > 1; level--)
				locksToAcquire.add(assemblyReadLocks[level]);
			break;

		case ST3:
			locksToAcquire.add(assemblyReadLocks[BASE_ASSEMBLY_LEVEL]);
			// Pre-lock all assembly levels to avoid deadlocks
			for (int level = Parameters.NumAssmLevels; level > 1; level--)
				locksToAcquire.add(assemblyReadLocks[level]);
			break;

		case ST4:
			locksToAcquire.add(assemblyReadLocks[BASE_ASSEMBLY_LEVEL]);
			locksToAcquire.add(documentReadLock);
			break;

		case ST5:
			locksToAcquire.add(assemblyReadLocks[BASE_ASSEMBLY_LEVEL]);
			locksToAcquire.add(compositePartReadLock);
			break;

		case ST8:
			locksToAcquire.add(assemblyWriteLocks[BASE_ASSEMBLY_LEVEL]);
			// Pre-lock all assembly levels to avoid deadlocks
			for (int level = Parameters.NumAssmLevels; level > 1; level--)
				locksToAcquire.add(assemblyWriteLocks[level]);
			break;

		case OP4:
		case OP5:
			locksToAcquire.add(manualReadLock);
			break;

		case OP6:
			break;

		case OP7:
			locksToAcquire.add(assemblyReadLocks[BASE_ASSEMBLY_LEVEL]);
			break;

		case OP8:
			locksToAcquire.add(compositePartReadLock);
			break;

		case OP11:
			locksToAcquire.add(manualWriteLock);
			break;

		case OP12:
			break;

		case OP13:
			locksToAcquire.add(assemblyWriteLocks[BASE_ASSEMBLY_LEVEL]);
			break;

		case OP14:
			locksToAcquire.add(compositePartWriteLock);
			break;

		default:
			throw new RuntimeError("Unknown operation: "
					+ op.getOperationId().toString());
		}
	}

	public int execute() throws OperationFailedException {
		try {

			for (Lock lock : locksToAcquire) lock.lock();
			return op.performOperation();
		} 
		finally {
			if (Parameters.sequentialReplayEnabled)
				lastOperationTimestamp = globalCounter.getAndIncrement();

			AssemblyLocksAcquired threadAssemblyLocksAcquired = 
				assemblyLocksAcquired.get();

			for (int level = 1; level <= Parameters.NumAssmLevels; level++) {
				if (threadAssemblyLocksAcquired.isReadAcquired[level])
					assemblyReadLocks[level].unlock();
				if (threadAssemblyLocksAcquired.isWriteAcquired[level])
					assemblyWriteLocks[level].unlock();
			}
			threadAssemblyLocksAcquired.clear();

			for (Lock lock : locksToAcquire) lock.unlock();
		}
	}

	public int getLastOperationTimestamp() {
		return lastOperationTimestamp;
	}
}
