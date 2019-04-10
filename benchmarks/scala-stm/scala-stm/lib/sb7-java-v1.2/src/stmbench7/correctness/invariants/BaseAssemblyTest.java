package stmbench7.correctness.invariants;

import stmbench7.Parameters;
import stmbench7.annotations.Immutable;
import stmbench7.annotations.ThreadLocal;
import stmbench7.core.BaseAssembly;
import stmbench7.core.ComplexAssembly;
import stmbench7.core.CompositePart;
import stmbench7.core.Module;

/**
 * Test of invariants of a base assembly.
 */
@Immutable
@ThreadLocal
public class BaseAssemblyTest extends InvariantTest {

	public static void checkInvariants(BaseAssembly assembly, boolean initial,
			ComplexAssembly parentAssembly, Module module, TraversedObjects traversedObjects) {

		traversedObjects.baseAssemblies.add(assembly);
		
		AssemblyTest.checkInvariants(assembly, initial, Parameters.MaxBaseAssemblies, parentAssembly, module);
		
		for(CompositePart component : assembly.getComponents())
			CompositePartTest.checkInvariants(component, initial, assembly, traversedObjects);
	}
}
