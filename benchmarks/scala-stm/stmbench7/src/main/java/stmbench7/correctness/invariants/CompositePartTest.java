package stmbench7.correctness.invariants;

import java.util.TreeSet;

import stmbench7.Parameters;
import stmbench7.annotations.Immutable;
import stmbench7.annotations.ThreadLocal;
import stmbench7.backend.ImmutableCollection;
import stmbench7.backend.LargeSet;
import stmbench7.core.AtomicPart;
import stmbench7.core.BaseAssembly;
import stmbench7.core.CompositePart;

/**
 * Test of invariants of a composite part.
 */
@Immutable
@ThreadLocal
public class CompositePartTest extends InvariantTest {

	public static void checkInvariants(CompositePart component, boolean initial, BaseAssembly aParent, 
			TraversedObjects traversedObjects) {

		traversedObjects.components.add(component);

		System.err.print("Component " + traversedObjects.components.size() + "\r");
			
		DesignObjTest.checkInvariants(component, initial, Parameters.MaxCompParts, 0, Integer.MAX_VALUE - 1);
		
		int id = component.getId(), buildDate = component.getBuildDate();
		int minOldDate = Parameters.MinOldCompDate, maxOldDate = Parameters.MaxOldCompDate,
			minYoungDate = Parameters.MinYoungCompDate, maxYoungDate = Parameters.MaxYoungCompDate;
		if(! initial) {
			if(minOldDate % 2 == 0) minOldDate--;
			if(maxOldDate % 2 != 0) maxOldDate++;
			if(minYoungDate % 2 == 0) minYoungDate--;
			if(maxYoungDate % 2 != 0) maxYoungDate++;
		}
		if( (buildDate < minOldDate|| buildDate > maxOldDate) &&
				(buildDate < minYoungDate || buildDate > maxYoungDate) )
			reportError(component, id, "wrong buildDate (" + buildDate + ")");

		ImmutableCollection<BaseAssembly> usedIn = component.getUsedIn();
		if(aParent != null && !usedIn.contains(aParent))
			reportError(component, id, "a BaseAssembly parent not in set usedIn");
		
		for(BaseAssembly assembly : usedIn) {
			if(! assembly.getComponents().contains(component))
				reportError(assembly, assembly.getId(), "a child CompositePart not in set of components");
		}
		
		DocumentationTest.checkInvariants(component.getDocumentation(), component, traversedObjects);
		
		LargeSet<AtomicPart> parts = component.getParts();
		if(! parts.contains(component.getRootPart()))
			reportError(component, id, "rootPart not in set of parts");
		
		TreeSet<AtomicPart> allConnectedParts = new TreeSet<AtomicPart>();
		for(AtomicPart part : parts)
			AtomicPartTest.checkInvariants(part, initial, component, allConnectedParts, traversedObjects);
		
		for(AtomicPart part : allConnectedParts)
			if(! parts.contains(part)) reportError(component, id, "a graph-connected AtomicPart not in set of all parts");
	}
}
