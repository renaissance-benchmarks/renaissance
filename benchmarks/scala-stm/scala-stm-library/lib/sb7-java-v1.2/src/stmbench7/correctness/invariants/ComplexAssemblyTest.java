package stmbench7.correctness.invariants;

import stmbench7.Parameters;
import stmbench7.annotations.Immutable;
import stmbench7.annotations.ThreadLocal;
import stmbench7.core.Assembly;
import stmbench7.core.BaseAssembly;
import stmbench7.core.ComplexAssembly;
import stmbench7.core.Module;

/**
 * Test of invariants of a complex assembly.
 */
@Immutable
@ThreadLocal
public class ComplexAssemblyTest extends InvariantTest {

	public static void checkInvariants(ComplexAssembly assembly, boolean initial, ComplexAssembly parentAssembly,
			Module module, TraversedObjects traversedObjects) {

		traversedObjects.complexAssemblies.add(assembly);
		
		AssemblyTest.checkInvariants(assembly, initial, Parameters.MaxComplexAssemblies, parentAssembly, module);
		
		int id = assembly.getId(), level = assembly.getLevel();
		if(level <= 1 || level > Parameters.NumAssmLevels)
			reportError(assembly, id, "level", 1, Parameters.NumAssmLevels, level);
		
		for(Assembly subAssembly : assembly.getSubAssemblies()) {
			if(level > 2) {
				if(! (subAssembly instanceof ComplexAssembly))
					reportError(assembly, id, "subAssembly not of type ComplexAssembly at level = " + level);
				ComplexAssemblyTest.checkInvariants((ComplexAssembly)subAssembly, initial, assembly, module, traversedObjects);
			}
			else {
				if(! (subAssembly instanceof BaseAssembly))
					reportError(assembly, id, "subAssembly not of type BaseAssembly at level = 2");
				BaseAssemblyTest.checkInvariants((BaseAssembly)subAssembly, initial, assembly, module, traversedObjects);
			}
		}
			
	}

}
