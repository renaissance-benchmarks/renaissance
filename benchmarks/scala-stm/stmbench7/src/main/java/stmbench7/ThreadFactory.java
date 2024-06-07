package stmbench7;

import stmbench7.annotations.NonAtomic;

/**
 * In most cases, the factory will simply create a java.lang.Thread object using
 * a given Runnable object. Some STMs, however, require that transactions are
 * executed by threads of a specified class (descendant from java.lang.Thread).
 */
@NonAtomic
public abstract class ThreadFactory {

	public static ThreadFactory instance = null;
	
	public static void setInstance(ThreadFactory newInstance) {
		instance = newInstance;
	}
	
	public abstract Thread createThread(Runnable runnable);
}
