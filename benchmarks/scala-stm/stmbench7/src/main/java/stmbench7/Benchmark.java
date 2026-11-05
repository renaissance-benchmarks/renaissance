package stmbench7;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Formatter;

import stmbench7.annotations.NonAtomic;
import stmbench7.backend.BackendFactory;
import stmbench7.core.DesignObjFactory;
import stmbench7.core.Operation;
import stmbench7.core.RuntimeError;
import stmbench7.correctness.invariants.CheckInvariantsOperation;
import stmbench7.correctness.opacity.SequentialReplayThread;
import stmbench7.correctness.opacity.StructureComparisonOperation;
import stmbench7.impl.NoSynchronizationInitializer;
import stmbench7.ThreadRandom.Phase;

/**
 * STMBench7 benchmark, the main program.
 * Run with argument "-h" or "--help" to see the syntax.
 *
 * Modified for Renaissance benchmark suite integration.
 */
@NonAtomic
public class Benchmark {

	public static final String VERSION = "1.0(15.02.2011)";

	public class BenchmarkParametersException extends Exception {
		private static final long serialVersionUID = 6341915439489283553L;

		public BenchmarkParametersException(String message, Exception cause) {
			super(message + ": " + cause.toString());
		}

		public BenchmarkParametersException(String message) {
			super(message);
		}

		public BenchmarkParametersException() {
			super("");
		}
	}

	/**
	 * Result container for benchmark execution.
	 */
	public static class Result {
		public final int successfulOperations;
		public final int failedOperations;
		public final double elapsedTime;
		public final boolean invariantsValid;
		public final String validationError;

		public Result(int successful, int failed, double elapsed) {
			this(successful, failed, elapsed, true, null);
		}

		public Result(int successful, int failed, double elapsed, boolean invariantsValid, String validationError) {
			this.successfulOperations = successful;
			this.failedOperations = failed;
			this.elapsedTime = elapsed;
			this.invariantsValid = invariantsValid;
			this.validationError = validationError;
		}
	}

	// Original main method preserved for standalone usage
	public static void main(String[] args) throws InterruptedException {
		Benchmark benchmark = null;
		ThreadRandom.phase = Phase.INIT;

		try {
			benchmark = new Benchmark(args);
		}
		catch(BenchmarkParametersException e) {
			System.err.println(e.getMessage());
			System.exit(1);
		}

		benchmark.createInitialClone();
		benchmark.start();
		benchmark.showTTCHistograms();
		benchmark.showStats();
	}

	// Made public for external access
	public SynchMethodInitializer synchMethodInitializer;
	public boolean printTTCHistograms = false;
	public double[] operationCDF;
	public BenchThread[] benchThreads;
	public Thread[] threads;
	public Setup setup, setupClone;
	public double elapsedTime;
	public int countOfOperations;

	/**
	 * Original constructor for command-line usage.
	 */
	private Benchmark(String[] args) throws BenchmarkParametersException, InterruptedException {
		printHeader();

		parseCommandLineParameters(args);
		printRunTimeParametersInformation();

		generateOperationCDF();
		setupStructures();
	}

	/**
	 * API constructor for programmatic usage (e.g., from Renaissance benchmark suite).
	 *
	 * @param numThreads Number of threads to use
	 * @param numSeconds Duration in seconds (used if countOfOperations <= 0)
	 * @param countOfOperations Number of operations per thread (if > 0, overrides numSeconds)
	 * @param workload Workload type: "r" (read-dominated), "rw" (read-write), "w" (write-dominated)
	 * @param synchronizationType Synchronization type enum value
	 * @param stmInitializerClassName Full class name of STM initializer (required if synchronizationType is STM)
	 * @param longTraversalsEnabled Enable long traversal operations
	 * @param structureModificationEnabled Enable structural modification operations
	 * @param sequentialReplayEnabled Enable sequential replay for opacity checking
	 */
	public Benchmark(
			int numThreads,
			int numSeconds,
			int countOfOperations,
			String workload,
			Parameters.SynchronizationType synchronizationType,
			String stmInitializerClassName,
			boolean longTraversalsEnabled,
			boolean structureModificationEnabled,
			boolean sequentialReplayEnabled
	) throws BenchmarkParametersException, InterruptedException {

		// Set parameters directly
		Parameters.numThreads = numThreads;
		Parameters.numSeconds = numSeconds;
		this.countOfOperations = countOfOperations;
		Parameters.longTraversalsEnabled = longTraversalsEnabled;
		Parameters.structureModificationEnabled = structureModificationEnabled;
		Parameters.sequentialReplayEnabled = sequentialReplayEnabled;
		Parameters.synchronizationType = synchronizationType;

		// Parse workload type
		if (workload != null) {
			if (workload.equals("r"))
				Parameters.workloadType = Parameters.WorkloadType.READ_DOMINATED;
			else if (workload.equals("rw"))
				Parameters.workloadType = Parameters.WorkloadType.READ_WRITE;
			else if (workload.equals("w"))
				Parameters.workloadType = Parameters.WorkloadType.WRITE_DOMINATED;
			else
				throw new BenchmarkParametersException("Invalid workload type: " + workload);
		}

		// Initialize synchronization method
		initializeSynchMethod(stmInitializerClassName);

		// Generate operation probability distribution
		generateOperationCDF();

		// Setup benchmark data structures
		setupStructures();
	}

	/**
	 * Initialize the synchronization method based on configuration.
	 */
	@SuppressWarnings("unchecked")
	private void initializeSynchMethod(String stmInitializerClassName) throws BenchmarkParametersException {
		Class<? extends SynchMethodInitializer> synchMethodInitializerClass = null;

		switch(Parameters.synchronizationType) {
			case NONE:
				synchMethodInitializerClass = ImplParameters.noSynchronizationInitializerClass;
				break;
			case LOCK_COARSE:
				synchMethodInitializerClass = ImplParameters.coarseGrainedLockingInitializerClass;
				break;
			case LOCK_MEDIUM:
				synchMethodInitializerClass = ImplParameters.mediumGrainedLockingInitializerClass;
				break;
			case LOCK_FINE:
				synchMethodInitializerClass = ImplParameters.fineGrainedLockingInitializerClass;
				break;
			case STM:
				if (stmInitializerClassName != null) {
					try {
						synchMethodInitializerClass =
								(Class<? extends SynchMethodInitializer>)
										Class.forName(stmInitializerClassName);
					}
					catch(ClassNotFoundException e) {
						throw new BenchmarkParametersException(
								"Error instantiating the STM initializer class", e);
					}
				}
				else if (ImplParameters.defaultSTMInitializerClass != null) {
					synchMethodInitializerClass = ImplParameters.defaultSTMInitializerClass;
				}
				else {
					throw new BenchmarkParametersException(
							"STM initializer class name not given and a default class not specified" +
									" in ImplParameters.defaultSTMInitializerClass");
				}
				break;
		}

		try {
			synchMethodInitializer =
					synchMethodInitializerClass.getDeclaredConstructor().newInstance();
		}
		catch(Exception e) {
			throw new BenchmarkParametersException("Error instantiating STM initializer class", e);
		}

		setFactoryInstances(synchMethodInitializer);
	}

	/**
	 * Reset benchmark state for a new iteration.
	 * Recreates BenchThread instances with fresh counters while reusing the Setup.
	 */
	public void resetForNextIteration() {
		for (int i = 0; i < benchThreads.length; i++) {
			benchThreads[i] = new BenchThread(setup, operationCDF, (short) i, countOfOperations);
			threads[i] = ThreadFactory.instance.createThread(benchThreads[i]);
		}
		// Reset operation type statistics
		for (OperationType type : OperationType.values()) {
			type.successfulOperations = 0;
			type.failedOperations = 0;
			type.maxttc = 0;
		}
		ThreadRandom.phase = stmbench7.ThreadRandom.Phase.INIT;
	}

	/**
	 * Run the benchmark and return results.
	 * This is the main execution method for API usage.
	 */
	public Result start() throws InterruptedException {
		System.err.println("\nBenchmark started.");
		ThreadRandom.startConcurrentPhase();

		long startTime = System.currentTimeMillis();

		for (Thread thread : threads) {
			thread.start();
		}

		for (Thread thread : threads) {
			thread.join();
		}

		//zrusit meranie casu?
		long endTime = System.currentTimeMillis();
		elapsedTime = ((double)(endTime - startTime)) / 1000.0;
		System.err.println("Benchmark completed.\n");

		return computeResult();
	}

	/**
	 * Compute and return the benchmark results.
	 */
	public Result computeResult() {
		int totalSuccessful = 0;
		int totalFailed = 0;

		OperationId[] operations = OperationId.values();
		for (OperationId operation : operations) {
			int opNumber = operation.ordinal();
			for (BenchThread thread : benchThreads) {
				totalSuccessful += thread.successfulOperations[opNumber];
				totalFailed += thread.failedOperations[opNumber];
			}
		}

		return new Result(totalSuccessful, totalFailed, elapsedTime);
	}

	// ==================== Original methods below ====================

	private void printHeader() {
		String header =
				"The STMBench7 Benchmark (Java version)\n" +
						"A benchmark for comparing synchronization techniques\n" +
						"Version: " + VERSION + "\n" +
						"More information: http://lpd.epfl.ch/site/research/tmeval\n" +
						"Copyright (C) 2006-2008 LPD, I&C, EPFL (http://lpd.epfl.ch)\n" +
						"Implemented by Michal Kapalka (http://kapalka.eu)\n"+
						"Updated by Vincent Gramoli for compliance with the VELOX stack";

		printLine('=');
		System.out.println(header);
		printLine('=');
		System.out.println();
	}

	@SuppressWarnings("unchecked")
	private void parseCommandLineParameters(String[] args) throws BenchmarkParametersException {
		int argNumber = 0;
		String workload = null, synchType = null, stmInitializerClassName = null;

		while(argNumber < args.length) {
			String currentArg = args[argNumber++];

			try {
				if(currentArg.equals("--help") || currentArg.equals("-h")) {
					printSyntax();
					throw new BenchmarkParametersException();
				}
				else if(currentArg.equals("--no-traversals")) Parameters.longTraversalsEnabled = false;
				else if(currentArg.equals("--no-sms")) Parameters.structureModificationEnabled = false;
				else if(currentArg.equals("--ttc-histograms")) printTTCHistograms = true;
				else if(currentArg.equals("--seq-replay")) Parameters.sequentialReplayEnabled = true;
				else if(currentArg.equals("--")) {
					Parameters.stmCommandLineParameters = new String[args.length - argNumber];
					int stmArgNum = 0;
					while(argNumber < args.length)
						Parameters.stmCommandLineParameters[stmArgNum++] = args[argNumber++];
					break;
				}
				else {
					String optionValue = args[argNumber++];
					if(currentArg.equals("-t")) Parameters.numThreads = Integer.parseInt(optionValue);
					else if(currentArg.equals("-l")) Parameters.numSeconds = Integer.parseInt(optionValue);
					else if(currentArg.equals("-w")) workload = optionValue;
					else if(currentArg.equals("-g")) synchType = optionValue;
					else if(currentArg.equals("-s")) stmInitializerClassName = optionValue;
					else if(currentArg.equals("-c")) countOfOperations = Integer.parseInt(optionValue);
					else throw new BenchmarkParametersException("Invalid option: " + currentArg);
				}
			}
			catch(IndexOutOfBoundsException e) {
				throw new BenchmarkParametersException("Missing value after option: " + currentArg);
			}
			catch(NumberFormatException e) {
				throw new BenchmarkParametersException("Number expected after option: " + currentArg);
			}
		}

		if(workload != null) {
			if(workload.equals("r"))
				Parameters.workloadType = Parameters.WorkloadType.READ_DOMINATED;
			else if(workload.equals("rw"))
				Parameters.workloadType = Parameters.WorkloadType.READ_WRITE;
			else if(workload.equals("w"))
				Parameters.workloadType = Parameters.WorkloadType.WRITE_DOMINATED;
			else throw new BenchmarkParametersException("Invalid workload type: " + workload);
		}

		if(synchType != null) {
			if(synchType.equals("coarse"))
				Parameters.synchronizationType = Parameters.SynchronizationType.LOCK_COARSE;
			else if(synchType.equals("medium"))
				Parameters.synchronizationType = Parameters.SynchronizationType.LOCK_MEDIUM;
			else if(synchType.equals("fine"))
				Parameters.synchronizationType = Parameters.SynchronizationType.LOCK_FINE;
			else if(synchType.equals("none"))
				Parameters.synchronizationType = Parameters.SynchronizationType.NONE;
			else if(synchType.equals("stm"))
				Parameters.synchronizationType = Parameters.SynchronizationType.STM;
			else throw new BenchmarkParametersException("Invalid lock granularity: " + synchType);
		}

		Class<? extends SynchMethodInitializer> synchMethodInitializerClass = null;
		switch(Parameters.synchronizationType) {
			case NONE:
				synchMethodInitializerClass = ImplParameters.noSynchronizationInitializerClass;
				break;
			case LOCK_COARSE:
				synchMethodInitializerClass = ImplParameters.coarseGrainedLockingInitializerClass;
				break;
			case LOCK_MEDIUM:
				synchMethodInitializerClass = ImplParameters.mediumGrainedLockingInitializerClass;
				break;
			case LOCK_FINE:
				synchMethodInitializerClass = ImplParameters.fineGrainedLockingInitializerClass;
				break;
			case STM:
				if(stmInitializerClassName != null) {
					try {
						synchMethodInitializerClass =
								(Class<? extends SynchMethodInitializer>)
										Class.forName(stmInitializerClassName);
					}
					catch(ClassNotFoundException e) {
						throw new BenchmarkParametersException("Error instantiating the STM" +
								" initializer class", e);
					}
				}
				else if(ImplParameters.defaultSTMInitializerClass != null) {
					synchMethodInitializerClass = ImplParameters.defaultSTMInitializerClass;
				}
				else throw new BenchmarkParametersException("STM initializer class name not given" +
							" and a default class not specified" +
							" in ImpParameters.defaultSTMInitializerClass");
				break;
		}
		try {
			synchMethodInitializer =
					synchMethodInitializerClass.getDeclaredConstructor().newInstance();
		}
		catch(Exception e) {
			throw new BenchmarkParametersException("Error instantiating STM initializer class", e);
		}

		setFactoryInstances(synchMethodInitializer);
	}

	public void setFactoryInstances(SynchMethodInitializer synchMethodInitializer) {
		DesignObjFactory.setInstance(synchMethodInitializer.createDesignObjFactory());
		BackendFactory.setInstance(synchMethodInitializer.createBackendFactory());
		OperationExecutorFactory.setInstance(synchMethodInitializer.createOperationExecutorFactory());
		ThreadFactory.setInstance(synchMethodInitializer.createThreadFactory());
	}

	private void printRunTimeParametersInformation() {
		printSection("Benchmark parameters");

		System.out.println("Number of threads: " + Parameters.numThreads + "\n" +
				"Length: " + Parameters.numSeconds + " s\n" +
				"Workload: " + Parameters.workloadType + "\n" +
				"Synchronization method: " + Parameters.synchronizationType + "\n" +
				"Long traversals " + (Parameters.longTraversalsEnabled ? "enabled" : "disabled") + "\n" +
				"Structural modification operations " +
				(Parameters.structureModificationEnabled ? "enabled" : "disabled") + "\n" +
				"DesignObjFactory: " + DesignObjFactory.instance.getClass().getName() + "\n" +
				"BackendFactory: " + BackendFactory.instance.getClass().getName() + "\n" +
				"OperationExecutorFactory: " +
				OperationExecutorFactory.instance.getClass().getName() + "\n" +
				"ThreadFactory: " + ThreadFactory.instance.getClass().getName() + "\n" +
				"Sequential replay " + (Parameters.sequentialReplayEnabled ? "enabled" : "disabled"));

		System.out.print("STM-specific parameters:");
		if(Parameters.stmCommandLineParameters == null) System.out.print(" none");
		else for(String parameter : Parameters.stmCommandLineParameters)
			System.out.print(" " + parameter);
		System.out.println("\n");
	}

	private void generateOperationCDF() {
		double shortTraversalsRatio = (double)Parameters.ShortTraversalsRatio / 100.0,
				operationsRatio = (double)Parameters.OperationsRatio / 100.0;

		double traversalsRatio, structuralModificationsRatio;
		if(Parameters.longTraversalsEnabled) traversalsRatio = (double)Parameters.TraversalsRatio / 100.0;
		else traversalsRatio = 0;
		if(Parameters.structureModificationEnabled)
			structuralModificationsRatio = (double)Parameters.StructuralModificationsRatio / 100.0;
		else structuralModificationsRatio = 0;

		double readOnlyOperationsRatio = (double)Parameters.workloadType.readOnlyOperationsRatio / 100.0,
				updateOperationsRatio = 1.0 - readOnlyOperationsRatio;

		double sumRatios = traversalsRatio + shortTraversalsRatio + operationsRatio +
				structuralModificationsRatio * updateOperationsRatio;
		traversalsRatio /= sumRatios;
		shortTraversalsRatio /= sumRatios;
		operationsRatio /= sumRatios;
		structuralModificationsRatio /= sumRatios;

		for (OperationType type : OperationType.values()) type.count = 0;
		OperationId[] operations = OperationId.values();
		for(OperationId operation : operations) operation.getType().count++;

		OperationType.TRAVERSAL.probability =
				traversalsRatio * updateOperationsRatio / OperationType.TRAVERSAL.count;
		OperationType.TRAVERSAL_RO.probability =
				traversalsRatio * readOnlyOperationsRatio / OperationType.TRAVERSAL_RO.count;
		OperationType.SHORT_TRAVERSAL.probability =
				shortTraversalsRatio * updateOperationsRatio / OperationType.SHORT_TRAVERSAL.count;
		OperationType.SHORT_TRAVERSAL_RO.probability =
				shortTraversalsRatio * readOnlyOperationsRatio / OperationType.SHORT_TRAVERSAL_RO.count;
		OperationType.OPERATION.probability =
				operationsRatio * updateOperationsRatio / OperationType.OPERATION.count;
		OperationType.OPERATION_RO.probability =
				operationsRatio * readOnlyOperationsRatio / OperationType.OPERATION_RO.count;
		OperationType.STRUCTURAL_MODIFICATION.probability =
				structuralModificationsRatio * updateOperationsRatio / OperationType.STRUCTURAL_MODIFICATION.count;

		System.out.println("Operation ratios [%]:");
		for(OperationType type : OperationType.values())
			System.out.println(alignText(type.toString(), 23) + ": " +
					formatDouble(type.probability * type.count * 100));
		System.out.println();

		double[] operationProbabilities = new double[operations.length];
		for(OperationId operation : operations) {
			double operationProbability = operation.getType().probability;
			operationProbabilities[operation.ordinal()] = operationProbability;
		}

		operationCDF = new double[operations.length];
		double prevProbValue = 0;
		for(int opNum = 0; opNum < operations.length; opNum++) {
			operationCDF[opNum] = prevProbValue + operationProbabilities[opNum];
			prevProbValue = operationCDF[opNum];
		}
		operationCDF[operations.length - 1] = 1.0; // to avoid rounding errors
	}

	private void setupStructures() throws InterruptedException {
		System.err.println("Setup start...");
		setup = new Setup();

		benchThreads = new BenchThread[Parameters.numThreads];
		threads = new Thread[Parameters.numThreads];
		for(short threadNum = 0; threadNum < Parameters.numThreads; threadNum++) {
			benchThreads[threadNum] =
					new BenchThread(setup, operationCDF, threadNum, countOfOperations);
			threads[threadNum] = ThreadFactory.instance.createThread(benchThreads[threadNum]);
		}
		System.err.println("Setup completed.");
	}

	public void checkInvariants(boolean initial) throws InterruptedException {
		if(initial) System.err.println("Checking invariants (initial data structure):");
		else System.err.println("Checking invariants (final data structure):");

		Operation checkInvariantsOperation =
				new CheckInvariantsOperation(setup, initial);
		OperationExecutorFactory.executeSequentialOperation(checkInvariantsOperation);
	}

	/**
	 * Validate invariants and return result with success/failure status.
	 * This is the preferred method for Renaissance integration.
	 *
	 * @param initial true if checking initial state, false for post-benchmark state
	 * @return Result containing validation status
	 */
	public Result validateInvariants(boolean initial) throws InterruptedException {
		Result currentResult = computeResult();

		try {
			if(initial) System.err.println("Checking invariants (initial data structure):");
			else System.err.println("Checking invariants (final data structure):");

			Operation checkInvariantsOperation =
					new CheckInvariantsOperation(setup, initial);
			OperationExecutorFactory.executeSequentialOperation(checkInvariantsOperation);

			// Invariants passed
			return new Result(
					currentResult.successfulOperations,
					currentResult.failedOperations,
					currentResult.elapsedTime,
					true,
					null
			);
		} catch (Exception e) {
			// Invariants failed
			return new Result(
					currentResult.successfulOperations,
					currentResult.failedOperations,
					currentResult.elapsedTime,
					false,
					e.getMessage()
			);
		}
	}

	public void createInitialClone() throws InterruptedException {
		if(! Parameters.sequentialReplayEnabled) return;

		System.err.println("Cloning the initial data structure...");
		ThreadRandom.reset();
		setFactoryInstances(new NoSynchronizationInitializer());
		setupClone = new Setup();
		setFactoryInstances(synchMethodInitializer);
		System.err.println("Cloning completed.");

		System.err.println("Checking if the clone is the same as the data structure...");
		StructureComparisonOperation structureComparisonOperation =
				new StructureComparisonOperation(setup, setupClone);
		OperationExecutorFactory.executeSequentialOperation(structureComparisonOperation);
		System.err.println("Check OK.");
	}

	private ArrayList<BenchThread.ReplayLogEntry> collectSortedReplayLog() {
		ArrayList<BenchThread.ReplayLogEntry> replayLog = new ArrayList<>();
		for (BenchThread thread : benchThreads)
			replayLog.addAll(thread.replayLog);
		Collections.sort(replayLog);
		return replayLog;
	}

	/**
	 * Check opacity by replaying operations sequentially and comparing results.
	 * Requires sequentialReplayEnabled to be true and createInitialClone() to be called first.
	 *
	 * @return true if opacity check passed, false otherwise
	 */
	public boolean checkOpacity() throws InterruptedException {
		if (!Parameters.sequentialReplayEnabled) {
			System.err.println("Sequential replay not enabled, skipping opacity check.");
			return true;
		}

		if (setupClone == null) {
			System.err.println("Initial clone not created, cannot check opacity. Call createInitialClone() first.");
			return false;
		}

		try {
			System.err.println("\nReplaying the execution in a single thread...");

			ArrayList<BenchThread.ReplayLogEntry> replayLog = collectSortedReplayLog();

			setFactoryInstances(new NoSynchronizationInitializer());
			ThreadRandom.startSequentialReplayPhase();
			SequentialReplayThread seqThread = new SequentialReplayThread(setupClone,
					operationCDF, replayLog);
			seqThread.run();
			setFactoryInstances(synchMethodInitializer);

			StructureComparisonOperation structureComparisonOperation =
					new StructureComparisonOperation(setup, setupClone);
			OperationExecutorFactory.executeSequentialOperation(structureComparisonOperation);
			return true;
		} catch (Exception e) {
			System.err.println("\nOpacity check failed: " + e.getMessage());
			return false;
		}
	}

	public void showTTCHistograms() {
		if(! printTTCHistograms) return;

		printSection("TTC histograms");

		OperationId[] operations = OperationId.values();
		for(OperationId operation : operations) {
			System.out.print("TTC histogram for " + operation + ":");

			for(int ttc = 0; ttc <= Parameters.MAX_LOW_TTC; ttc++) {
				int count = 0;
				for(BenchThread thread : benchThreads)
					count += thread.operationsTTC[operation.ordinal()][ttc];

				System.out.print(" " + ttc + "," + count);
			}

			for(int logTtcIndex = 0; logTtcIndex < Parameters.HIGH_TTC_ENTRIES; logTtcIndex++) {
				int count = 0;
				for(BenchThread thread : benchThreads)
					count += thread.operationsHighTTCLog[operation.ordinal()][logTtcIndex];

				int ttc = logTtcIndex2Ttc(logTtcIndex);
				System.out.print(" " + ttc + "," + count);
			}

			System.out.println();
		}
		System.out.println();
	}

	private int logTtcIndex2Ttc(double logTtcIndex) {
		return (int)((Parameters.MAX_LOW_TTC + 1) * Math.pow(Parameters.HIGH_TTC_LOG_BASE, logTtcIndex));
	}

	public void showStats() {
		printSection("Detailed results");

		OperationId[] operations = OperationId.values();
		for(OperationId operation : operations) {
			System.out.print("Operation " + alignText(operation.toString(), 4) + ":   ");

			int opNumber = operation.ordinal();
			int successful = 0, failed = 0, maxttc = 0;
			for(BenchThread thread : benchThreads) {
				successful += thread.successfulOperations[opNumber];
				failed += thread.failedOperations[opNumber];
				maxttc = Math.max(maxttc, computeMaxThreadTTC(thread, opNumber));
			}

			System.out.println("successful = " + successful + "\tmaxttc = " + maxttc + "\tfailed = " + failed);

			OperationType operationType = operation.getType();
			operationType.successfulOperations += successful;
			operationType.failedOperations += failed;
			operationType.maxttc = Math.max(operationType.maxttc, maxttc);
		}
		System.out.println();

		printSection("Sample errors (operation ratios [%])");

		int totalSuccessful = 0, totalFailed = 0;
		for(OperationType type : OperationType.values()) {
			totalSuccessful += type.successfulOperations;
			totalFailed += type.failedOperations;
		}

		double totalError = 0, totalTError = 0;
		for(OperationType type : OperationType.values()) {
			double expectedRatio = type.probability * type.count * 100.0;
			double realRatio = (double)type.successfulOperations / (double)totalSuccessful * 100.0;
			double error = Math.abs(realRatio - expectedRatio);
			double tRealRatio = (double)(type.successfulOperations + type.failedOperations) /
					(double)(totalSuccessful + totalFailed) * 100.0;
			double tError = Math.abs(tRealRatio - expectedRatio);
			System.out.println(alignText(type.toString(), 23) + ":  " +
					"expected = " + formatDouble(expectedRatio) +
					"\tsuccessful = " + formatDouble(realRatio) +
					"\terror = " + formatDouble(error) +
					"\t(total = " + formatDouble(tRealRatio) +
					"\terror = " + formatDouble(tError) + ")");
			totalError += error;
			totalTError += tError;
		}
		System.out.println();

		printSection("Summary results");

		int total = totalSuccessful + totalFailed;
		for(OperationType type : OperationType.values()) {
			int totalTypeOperations = type.successfulOperations + type.failedOperations;
			System.out.println(alignText(type.toString(), 23) + ":  " +
					"successful = " + type.successfulOperations +
					"\tmaxttc = " + type.maxttc +
					"\tfailed = " + type.failedOperations +
					"\ttotal = " + totalTypeOperations);
		}
		System.out.println();

		System.out.println("Total sample error: " + formatDouble(totalError) + "%" +
				" (" + formatDouble(totalTError) + "% including failed)");
		System.out.println("Total throughput: " + formatDouble( (double)totalSuccessful / elapsedTime ) + " op/s" +
				" (" + formatDouble( (double)total / elapsedTime ) + " op/s including failed)");
		System.out.println("Elapsed time: " + formatDouble(elapsedTime) + " s");
	}

	private int computeMaxThreadTTC(BenchThread thread, int opNumber) {
		for(int logTtcIndex = Parameters.HIGH_TTC_ENTRIES - 1; logTtcIndex >= 0; logTtcIndex--) {
			if(thread.operationsHighTTCLog[opNumber][logTtcIndex] > 0)
				return logTtcIndex2Ttc(logTtcIndex);
		}

		for(int ttc = Parameters.MAX_LOW_TTC; ttc >= 0; ttc--) {
			if(thread.operationsTTC[opNumber][ttc] > 0) return ttc;
		}

		return 0; // operation never completed with success
	}

	private void printSyntax() {
		String syntax =
				"Syntax:\n" +
						"java stmbench7.Benchmark [options] [-- stm-specific options]\n\n" +
						"Options:\n" +
						"\t-t numThreads -- set the number of threads (default: 1)\n" +
						"\t-l length     -- set the length of the benchmark, in seconds (default: 10)\n" +
						"\t-c count      -- set the length of the benchmark, in operations\n" +
						"\t-w r|rw|w     -- set the workload: r = read-dominated, w = write-dominated\n" +
						"\t                                   rw = read-write (default: read-dominated)\n" +
						"\t-g coarse|medium|fine|none|stm -- set synchronization method (default: coarse)\n" +
						"\t-s stmInitializerClass         -- set STM initializer class (default: none)\n" +
						"\t--no-traversals  -- do not use long traversals\n" +
						"\t--no-sms         -- do not use structural modification operations\n" +
						"\t--seq-replay     -- replay the execution in a single thread\n" +
						"\t                    (checks for opacity violations)\n" +
						"\t--ttc-histograms -- print TTC histograms to stdout\n\n" +
						"Note: the benchmark needs a lot of lot of memory, so the -Xmx option of Java\n" +
						"might be necessary.";
		System.err.println(syntax);
	}

	private void printSection(String title) {
		printLine('-');
		System.out.println(title);
		printLine('-');
	}

	private void printLine(char ch) {
		StringBuffer line = new StringBuffer(79);
		for(int i = 0; i < 79; i++) line.append(ch);
		System.out.println(line);
	}

	private String alignText(String text, int width) {
		int textLen = text.length();
		int padding = width - textLen;
		if(padding < 0) throw new RuntimeError("alignText: width too small!");

		StringBuffer output = new StringBuffer(width);
		for(int i = 0; i < padding; i++) output.append(' ');
		output.append(text);

		return output.toString();
	}

	private String formatDouble(double number) {
		Formatter formatter = new Formatter();
		formatter.format("%3.2f", number);
		return formatter.toString();
	}
}