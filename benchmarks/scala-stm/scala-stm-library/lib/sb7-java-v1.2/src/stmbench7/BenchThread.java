package stmbench7;

import java.lang.reflect.Constructor;
import java.util.ArrayList;

import stmbench7.annotations.NonAtomic;
import stmbench7.core.Operation;
import stmbench7.core.RuntimeError;
import stmbench7.core.OperationFailedException;

/**
 * A single thread of the STMBench7 benchmark. Executes operations assigned to
 * it one by one, randomly choosing the next operation and respecting the
 * expected ratios of operations' counts.
 */
@NonAtomic
public class BenchThread implements Runnable {

	protected volatile boolean stop = false;
	protected double[] operationCDF;
	protected OperationExecutor[] operations;
	protected final short myThreadNum;
  protected final int countOfOperations;

	public int[] successfulOperations, failedOperations;
	public int[][] operationsTTC, operationsHighTTCLog;

	public class ReplayLogEntry implements Comparable<ReplayLogEntry> {
		public final short threadNum;
		public final int timestamp, result;
		public final boolean failed;
		public final int opNum;

		public ReplayLogEntry(int timestamp, int result, boolean failed,
				int opNum) {
			this.threadNum = myThreadNum;
			this.timestamp = timestamp;
			this.result = result;
			this.failed = failed;
			this.opNum = opNum;
		}

		public int compareTo(ReplayLogEntry entry) {
			return timestamp - entry.timestamp;
		}
	}

	public ArrayList<ReplayLogEntry> replayLog;

	public BenchThread(Setup setup, double[] operationCDF, short myThreadNum, int countOfOperations) {
		this.operationCDF = operationCDF;

		int numOfOperations = OperationId.values().length;
		operationsTTC = new int[numOfOperations][Parameters.MAX_LOW_TTC + 1];
		operationsHighTTCLog = new int[numOfOperations][Parameters.HIGH_TTC_ENTRIES];
		successfulOperations = new int[numOfOperations];
		failedOperations = new int[numOfOperations];
		operations = new OperationExecutor[numOfOperations];
		this.myThreadNum = myThreadNum;
    this.countOfOperations = countOfOperations;

		createOperations(setup);

		if (Parameters.sequentialReplayEnabled)
			replayLog = new ArrayList<ReplayLogEntry>();
	}

	protected BenchThread(Setup setup, double[] operationCDF) {
		this.operationCDF = operationCDF;
		operations = new OperationExecutor[OperationId.values().length];
		createOperations(setup);
		myThreadNum = 0;
    throw new RuntimeException("This ctor is no longer allowed.");
	}

	public void run() {
		int i = 0;
    int iteration = 0;
		while (!stop && iteration < countOfOperations) {
      iteration++;
			//if (i++ > 55) continue;
			int operationNumber = getNextOperationNumber(iteration);

			OperationType type = OperationId.values()[operationNumber].getType();
      // System.out.println(iteration + ": " + operationNumber + ", " + type);
			//if( (type != OperationType.SHORT_TRAVERSAL) ) continue;
			//		(type != OperationType.SHORT_TRAVERSAL_RO) &&
			//		(type != OperationType.OPERATION) )
			//	continue;

			//System.out.println(i + " > "
			//		+ OperationId.values()[operationNumber]);

			OperationExecutor currentExecutor = operations[operationNumber];
			int result = 0;
			boolean failed = false;

			try {
				long startTime = System.currentTimeMillis();

				result = currentExecutor.execute();

				long endTime = System.currentTimeMillis();
				//System.out.println("success");

				successfulOperations[operationNumber]++;
				int ttc = (int) (endTime - startTime);
				if (ttc <= Parameters.MAX_LOW_TTC)
					operationsTTC[operationNumber][ttc]++;
				else {
					double logHighTtc = (Math.log(ttc) - Math
							.log(Parameters.MAX_LOW_TTC + 1))
							/ Math.log(Parameters.HIGH_TTC_LOG_BASE);
					int intLogHighTtc = Math.min((int) logHighTtc,
							Parameters.HIGH_TTC_ENTRIES - 1);
					operationsHighTTCLog[operationNumber][intLogHighTtc]++;
				}
			} catch (OperationFailedException e) {
				failedOperations[operationNumber]++;
				failed = true;
			}

			if (Parameters.sequentialReplayEnabled) {
				ReplayLogEntry newEntry = new ReplayLogEntry(
						currentExecutor.getLastOperationTimestamp(), result, failed,
						operationNumber);
				replayLog.add(newEntry);
				//System.out.println("ts: " + newEntry.timestamp);
			}
		}
		System.err.println("Thread #" + myThreadNum + " finished.");
		//i = 0;
		//for (ReplayLogEntry entry : replayLog)
		//	System.out.println(i++ + " % " + OperationId.values()[entry.opNum]
		//			+ " -- " + entry.timestamp);
	}

	public void stopThread() {
		stop = true;
	}

	protected void createOperations(Setup setup) {
		for (OperationId operationDescr : OperationId.values()) {
			Class<? extends Operation> operationClass = operationDescr
					.getOperationClass();
			int operationIndex = operationDescr.ordinal();

			try {
				Constructor<? extends Operation> operationConstructor = operationClass
						.getConstructor(Setup.class);
				Operation operation = operationConstructor.newInstance(setup);

				operations[operationIndex] = OperationExecutorFactory.instance
						.createOperationExecutor(operation);
				assert (operation.getOperationId().getOperationClass()
						.equals(operationClass));
			} catch (Exception e) {
				throw new RuntimeError("Error while creating operation "
						+ operationDescr, e);
			}
		}
	}

	protected int getNextOperationNumber(int iteration) {
		// double whichOperation = ThreadRandom.nextDouble();
    double whichOperation = (iteration % 20) / 20.0;
		int operationNumber = 0;
		while (whichOperation >= operationCDF[operationNumber])
			operationNumber++;
		return operationNumber;
	}
}
