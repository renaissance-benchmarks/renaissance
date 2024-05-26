package stmbench7.correctness.invariants;

import stmbench7.annotations.Immutable;
import stmbench7.annotations.ThreadLocal;
import stmbench7.core.Manual;
import stmbench7.core.Module;

/**
 * Test of invariants of a manual.
 */
@Immutable
@ThreadLocal
public class ManualTest extends InvariantTest {

	public static void checkInvariants(Manual manual, Module module) {
		int id = manual.getId();
		if(id != 1) reportError(manual, id, "id", 1, id);
		
		String title = manual.getTitle(),
			titleShouldBe = "Manual for module #1";
		if(! title.equals(titleShouldBe))
			reportError(manual, id, "title", titleShouldBe, title);
		
		if(!manual.startsWith('I') && !manual.startsWith('i'))
			reportError(manual, id, "text (prefix)", "'I' || 'i'", manual.getText().substring(0, 7) + " ...");
		
		if(manual.startsWith('I') && manual.countOccurences('i') > 0)
			reportError(manual, id, "text starts from 'I' but contains 'i'");
		
		if(manual.startsWith('i') && manual.countOccurences('I') > 0)
			reportError(manual, id, "text starts from 'i' but contains 'I'");
		
		if(manual.getModule() != module)
			reportError(manual, id, "invalid connection to Module");
	}
}
