package stmbench7.core;

import stmbench7.annotations.Immutable;
import stmbench7.annotations.ThreadLocal;

/**
 * STMBench7 specific error. Indicates a serious problem, i.e., a violation of
 * the data structure invariants, which causes the benchmark to terminate.
 */
@Immutable
@ThreadLocal
public class RuntimeError extends Error {

	private static final long serialVersionUID = -5671909838938354776L;

	public RuntimeError() {
	}

	public RuntimeError(String message) {
		super(message);
	}

	public RuntimeError(Throwable cause) {
		super(cause);
	}

	public RuntimeError(String message, Throwable cause) {
		super(message, cause);
	}

}
