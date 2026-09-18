package stmbench7;

import stmbench7.annotations.NonAtomic;
import stmbench7.core.Operation;
import stmbench7.core.OperationFailedException;
import stmbench7.core.RuntimeError;

/**
 * Creates an OperationExecutor object, which is used
 * to execute the benchmark operations. For the default
 * implementation, see stmbench7.impl.DefaultOperationExecutorFactory.
 */
@NonAtomic
public abstract class OperationExecutorFactory {

	public static OperationExecutorFactory instance = null;
	
	public static void setInstance(OperationExecutorFactory newInstance) {
		instance = newInstance;
	}
	
	public abstract OperationExecutor createOperationExecutor(Operation op);
	
	public static void executeSequentialOperation(final Operation op) throws InterruptedException {
		final Throwable[] threadError = new Throwable[1];
		Thread opThread = ThreadFactory.instance.createThread(new Runnable() {
			public void run() {
				OperationExecutor operationExecutor =
					instance.createOperationExecutor(op);
				try {
					operationExecutor.execute();
				}
				catch(OperationFailedException e) {
					throw new RuntimeError("Unexpected failure of a sequential operation " + op);
				}
			}
		});
		opThread.setUncaughtExceptionHandler(new Thread.UncaughtExceptionHandler() {
			public void uncaughtException(Thread t, Throwable e) {
				threadError[0] = e;
			}
		});
		opThread.start();
		opThread.join();
		if (threadError[0] != null) {
			if (threadError[0] instanceof RuntimeError)
				throw (RuntimeError) threadError[0];
			throw new RuntimeError("Sequential operation failed: " + op, threadError[0]);
		}
	}
}
