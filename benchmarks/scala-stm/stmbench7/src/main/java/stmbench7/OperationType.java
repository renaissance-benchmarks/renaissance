package stmbench7;

import stmbench7.annotations.NonAtomic;

/**
 * Types of STMBench7 operations. The "RO" suffix means "read-only".
 */
@NonAtomic
public enum OperationType {
	TRAVERSAL, TRAVERSAL_RO, 
	SHORT_TRAVERSAL, SHORT_TRAVERSAL_RO,
	OPERATION, OPERATION_RO,
	STRUCTURAL_MODIFICATION;
	
	/**
	 * Some helper fields to make life easier.
	 */
	public int count = 0;
	public double probability = 0;
	public int successfulOperations = 0, failedOperations = 0, maxttc = 0;
}