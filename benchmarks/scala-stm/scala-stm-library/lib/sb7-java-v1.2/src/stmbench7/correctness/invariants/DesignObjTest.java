package stmbench7.correctness.invariants;

import stmbench7.Parameters;
import stmbench7.annotations.Immutable;
import stmbench7.annotations.ThreadLocal;
import stmbench7.core.DesignObj;

/**
 * Test of common invariants of elements inherited from a design object.
 */
@Immutable
@ThreadLocal
public class DesignObjTest extends InvariantTest {

	public static void checkInvariants(DesignObj obj, boolean initial, int maxId, int minBuildDate, int maxBuildDate) {
		int id = obj.getId();
		if(id < 1 || id > maxId) reportError(obj, id, "id", 1, maxId, id);
		
		String type = obj.getType();
		if(! checkType(type)) reportError(obj, id, "type", "type #(num)", type);
		
		int buildDate = obj.getBuildDate();
		if(! initial) {
			if(minBuildDate % 2 == 0) minBuildDate--;
			if(maxBuildDate % 2 != 0) maxBuildDate++;
		}
		if(buildDate < minBuildDate || buildDate > maxBuildDate)
			reportError(obj, id, "buildDate", minBuildDate, maxBuildDate, buildDate);
	}
	
	protected static boolean checkType(String type) {
		if(! type.startsWith("type #")) return false;
		
		try {
			int typeNum = Integer.parseInt(type.substring("type #".length()));
			if(typeNum < 0 || typeNum >= Parameters.NumTypes) return false;
			
		}
		catch(NumberFormatException e) {
			return false;
		}
		
		return true;
	}
}
