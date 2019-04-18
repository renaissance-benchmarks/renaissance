package stmbench7;

import stmbench7.annotations.Immutable;

/**
 * Parameters of the STMBench7 benchmark (see the specification).
 */
@Immutable
public class Parameters {

	/**
	 * OO7 benchmark parameters for the "medium" size of the benchmark.
	 * Can be adjusted to match larger or smaller applications.
	 * Note: these values describe the data structure only at its initial
	 * state, before the first structure modification operation completes
	 * with success.
	 */
	public static final int NumAtomicPerComp = 200,
		NumConnPerAtomic = 6,
		DocumentSize = 20000,
		ManualSize = 1000000,
		NumCompPerModule = 500,
		NumAssmPerAssm = 3,
		NumAssmLevels = 7,
		NumCompPerAssm = 3,
		NumModules = 1;	// currently not used (only a single module)

	/**
	 * Values derived from the OO7 parameters. Valid only before the first
	 * structure modification operation finishes with success.
	 */
	public static final int InitialTotalCompParts = NumModules * NumCompPerModule,
		InitialTotalBaseAssemblies = (int)Math.pow(NumAssmPerAssm, NumAssmLevels - 1),
		InitialTotalComplexAssemblies = 
			(1 - (int)Math.pow(NumAssmPerAssm, NumAssmLevels - 1)) / (1 - NumAssmPerAssm);

	/**
	 * Parameters defining how the size of the data structure can deviate
	 * from its initial size. Defines the size of the id pools.
	 */
	public static final int MaxCompParts = (int)(1.05 * InitialTotalCompParts),
		MaxAtomicParts = MaxCompParts * NumAtomicPerComp,
		MaxBaseAssemblies = (int)(1.05 * InitialTotalBaseAssemblies),
		MaxComplexAssemblies = (int)(1.05 * InitialTotalComplexAssemblies);

	/**
	 * Constants used in various operations (values taken from the
	 * original OO7 source code).
	 */
    public static final int MinModuleDate = 1000,
		MaxModuleDate = 1999,
		MinAssmDate = 1000,
		MaxAssmDate = 1999,
		MinAtomicDate = 1000,
		MaxAtomicDate = 1999,
		MinOldCompDate = 0,
		MaxOldCompDate = 999,
		MinYoungCompDate = 2000,
		MaxYoungCompDate = 2999,
		YoungCompFrac = 10,
		TypeSize = 10,
		NumTypes = 10,
		XYRange = 100000,
		TitleSize = 40;
    
    /**
     * Ratios of various operation types (in percents).
     */
    public static final int TraversalsRatio = 5,
    	ShortTraversalsRatio = 40,
    	OperationsRatio = 45,
    	StructuralModificationsRatio = 10;
    
    /**
     * Application workload.
     */
    @Immutable
    public enum WorkloadType {
    	READ_DOMINATED(90), 
    	READ_WRITE(60), 
    	WRITE_DOMINATED(10);
    	
    	public final int readOnlyOperationsRatio;
    	
    	private WorkloadType(int readOnlyOperationsRatio) {
    		this.readOnlyOperationsRatio = readOnlyOperationsRatio;
    	}
    }
    
    /**
     * Synchronization type.
     */
    @Immutable
    public enum SynchronizationType {
    	NONE, LOCK_COARSE, LOCK_MEDIUM, LOCK_FINE, STM;
    }
    
    /**
     * Command-line benchmark parameters.
     */
    public static WorkloadType workloadType = WorkloadType.READ_DOMINATED;
    public static SynchronizationType synchronizationType = SynchronizationType.LOCK_COARSE;
    public static int numThreads = 1, 
    	numSeconds = 10;
    public static boolean longTraversalsEnabled = true,
    	structureModificationEnabled = true,
    	sequentialReplayEnabled = false;

    /**
     * STM-specific command-line parameters.
     * To be parsed by a given STM initializer.
     */
    public static String[] stmCommandLineParameters = null;
    
    /**
     * Parameters of the output TTC histograms.
     */
	public static final int MAX_LOW_TTC = 999;
	public static final int HIGH_TTC_ENTRIES = 200;
	public static final double HIGH_TTC_LOG_BASE = 1.03;
}
