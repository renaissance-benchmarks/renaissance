package stmbench7;

import stmbench7.annotations.Immutable;
import stmbench7.core.RuntimeError;

/**
 * This is a central repository for thread-local random
 * number generators. No other class should create an instance
 * of class Random, but should use the methods in ThreadRandom
 * instead. This way we can centrally control the (un)determinism
 * of the benchmark and the implementation of a random number
 * generator used.
 */
@Immutable
public class ThreadRandom {

	public static enum Phase {
		INIT,
		CONCURRENT,
		SEQUENTIAL_REPLAY
	}
	
	// Custom LCG matching java.util.Random's algorithm. Uses a primitive long
	// for state so that Object.clone() performs a true value copy - unlike
	// java.util.Random whose AtomicLong seed is shared across shallow clones,
	// which would silently prevent restoreState() from working during STM retries.
	private static class CloneableRandom implements Cloneable {
		private static final long multiplier = 0x5DEECE66DL;
		private static final long addend     = 0xBL;
		private static final long mask       = (1L << 48) - 1;

		private long seed;

		public CloneableRandom(long seed) {
			this.seed = (seed ^ multiplier) & mask;
		}

		private int next(int bits) {
			seed = (seed * multiplier + addend) & mask;
			return (int)(seed >>> (48 - bits));
		}

		public int nextInt(int n) {
			if ((n & -n) == n) return (int)((n * (long)next(31)) >> 31);
			int bits, val;
			do {
				bits = next(31);
				val  = bits % n;
			} while (bits - val + (n - 1) < 0);
			return val;
		}

		public double nextDouble() {
			return (((long)(next(26)) << 27) + next(27)) / (double)(1L << 53);
		}

		@Override
		public CloneableRandom clone() {
			try {
				return (CloneableRandom) super.clone(); // seed is a long primitive -> deep copy
			}
			catch(CloneNotSupportedException e) {
				throw new RuntimeException(e);
			}
		}
	}
	
	private static class RandomState {
		private CloneableRandom currentState, savedState;
		public long callCount = 0;

		public RandomState() {
			currentState = new CloneableRandom(3);
			savedState = null;
		}

		public void saveState() {
			savedState = currentState.clone();
		}

		public void restoreState() {
			currentState = savedState;
		}
	}
	
	public static Phase phase = Phase.INIT;
	private static RandomState initRandom = new RandomState();
	private static short currentVirtualThreadNumber;
	private static RandomState[] virtualRandom;
	
	private ThreadRandom() { }
	
	private static final ThreadLocal<RandomState> random = 
		new ThreadLocal<RandomState>() {
			@Override
			protected RandomState initialValue() {
				return new RandomState();
			}
	};
	
	public static int nextInt(int n) {
		RandomState rs = getCurrentRandom();
		rs.callCount++;
		return rs.currentState.nextInt(n);
	}

	public static double nextDouble() {
		RandomState rs = getCurrentRandom();
		rs.callCount++;
		return rs.currentState.nextDouble();
	}

	public static long getCallCount() {
		return getCurrentRandom().callCount;
	}

	public static void reset() {
		if(phase != Phase.INIT) {
			System.out.println("Warning, cannot reset!");
			throw new RuntimeError("Cannot reset ThreadRandom after the initialization phase");
		}
		initRandom = new RandomState();
	}
	
	public static void startConcurrentPhase() {
		phase = Phase.CONCURRENT;
	}
	
	public static void startSequentialReplayPhase() {
		phase = Phase.SEQUENTIAL_REPLAY;
		virtualRandom = new RandomState[Parameters.numThreads];
		for(int n = 0; n < Parameters.numThreads; n++)
			virtualRandom[n] = new RandomState();
	}

	public static void setVirtualThreadNumber(short threadNum) {
		currentVirtualThreadNumber = threadNum;
	}
	
	public static void saveState() {
		getCurrentRandom().saveState();
	}
	
	public static void restoreState() {
		getCurrentRandom().restoreState();
	}
	
	private static RandomState getCurrentRandom() {
		/*
		switch(phase) {
		case INIT: return initRandom;
		case CONCURRENT: return random.get();
		case SEQUENTIAL_REPLAY: return virtualRandom[currentVirtualThreadNumber];
		default: return null;
		}
		*/
		switch(((Enum)phase).ordinal()) {
		case 0: return initRandom;
		case 1: return random.get();
		case 2: return virtualRandom[currentVirtualThreadNumber];
		default: return null;
		}
	}
}
