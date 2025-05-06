package stmbench7.correctness.invariants;

import stmbench7.annotations.Immutable;
import stmbench7.annotations.ThreadLocal;
import stmbench7.core.RuntimeError;

/**
 * Helper methods for all invariant tests.
 */
@Immutable
@ThreadLocal
public class InvariantTest {

	protected static void reportError(Object obj, int id, String message) {
		String withId = "";
		if(id > 0) withId = " with id = " + id;
		throw new RuntimeError("Invariant violated! Object " + obj.getClass().getName() + 
				withId + ": " + message);
	}
	
	protected static void reportError(Object obj, int id, String attribute, int expected, int found) {
		reportError(obj, id, "attribute " + attribute + 
				" --> expected value = " + expected + ", found = " + found);
	}
	
	protected static void reportError(Object obj, int id, String attribute, int expectedMin, int expectedMax, int found) {
		reportError(obj, id, "attribute " + attribute + 
				" --> expected value in [" + expectedMin + "," + expectedMax + "], found = " + found);
	}
	
	protected static void reportError(Object obj, int id, String attribute, String expected, String found) {
		reportError(obj, id, "attribute " + attribute + 
				" --> expected value = " + expected + ", found = " + found);
	}
}
