package stmbench7;

import stmbench7.annotations.NonAtomic;
import stmbench7.annotations.ThreadLocal;
import stmbench7.impl.NoSynchronizationInitializer;
import stmbench7.locking.CGLockingInitializer;
import stmbench7.locking.MGLockingInitializer;

/**
 * Parameters that describe the synchronization techniques
 * compiled in the benchmark.
 */
@NonAtomic
@ThreadLocal
public class ImplParameters {

	public static final Class<? extends SynchMethodInitializer>
		noSynchronizationInitializerClass = NoSynchronizationInitializer.class,
		coarseGrainedLockingInitializerClass = CGLockingInitializer.class,
		mediumGrainedLockingInitializerClass = MGLockingInitializer.class,
		fineGrainedLockingInitializerClass = null; // not implemented yet
	
	/**
	 * If non-null, the STM initializer does not have to be specified
	 * each time the benchmark is run with the "-g stm" command-line
	 * parameter.
	 */
	public static final Class<? extends SynchMethodInitializer>
		defaultSTMInitializerClass = null;
}
