package stmbench7.correctness.invariants;

import stmbench7.Parameters;
import stmbench7.annotations.Immutable;
import stmbench7.annotations.ThreadLocal;
import stmbench7.core.Assembly;
import stmbench7.core.ComplexAssembly;
import stmbench7.core.Module;

/**
 * Test of invariants of an assembly.
 */
@Immutable
@ThreadLocal
public class AssemblyTest extends InvariantTest {

	public static void checkInvariants(Assembly assembly, boolean initial, int maxId,
			ComplexAssembly parentAssembly, Module module) {

		DesignObjTest.checkInvariants(assembly, initial, maxId, Parameters.MinAssmDate, Parameters.MaxAssmDate);
		
		int id = assembly.getId();
		
		if(assembly.getSuperAssembly() != parentAssembly)
			reportError(assembly, id, "invalid reference to the parent ComplexAssembly");
		
		if(assembly.getModule() != module)
			reportError(assembly, id, "invalid reference to the parent Module");
	}

}
