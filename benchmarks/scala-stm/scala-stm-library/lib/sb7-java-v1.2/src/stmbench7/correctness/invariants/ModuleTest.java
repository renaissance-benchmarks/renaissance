package stmbench7.correctness.invariants;

import stmbench7.Parameters;
import stmbench7.annotations.Immutable;
import stmbench7.annotations.ThreadLocal;
import stmbench7.core.ComplexAssembly;
import stmbench7.core.Manual;
import stmbench7.core.Module;

/**
 * Test of invariants of the module. Starts a recursive
 * invariant check down the whole data structure.
 */
@Immutable
@ThreadLocal
public class ModuleTest extends InvariantTest {

	public static void checkInvariants(Module module, boolean initial, TraversedObjects traversedObjects) {
		DesignObjTest.checkInvariants(module, initial, 1, Parameters.MinModuleDate, Parameters.MaxModuleDate);
		
		int id = module.getId();
		Manual manual = module.getManual();
		if(manual == null) reportError(module, id, "Null manual in a module");
		ManualTest.checkInvariants(manual, module);
		
		ComplexAssembly rootAssembly = module.getDesignRoot();
		if(rootAssembly == null) reportError(module, id, "Null root assembly");
		ComplexAssemblyTest.checkInvariants(rootAssembly, initial, null, module, traversedObjects);
	}
}
