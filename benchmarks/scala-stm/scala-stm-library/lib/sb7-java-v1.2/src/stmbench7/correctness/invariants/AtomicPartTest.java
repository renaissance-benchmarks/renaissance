package stmbench7.correctness.invariants;

import java.util.TreeSet;

import stmbench7.Parameters;
import stmbench7.annotations.Immutable;
import stmbench7.annotations.ThreadLocal;
import stmbench7.backend.ImmutableCollection;
import stmbench7.core.AtomicPart;
import stmbench7.core.CompositePart;
import stmbench7.core.Connection;

/**
 * Test of invariants of an atomic part.
 */
@Immutable
@ThreadLocal
public class AtomicPartTest extends InvariantTest {

	public static void checkInvariants(AtomicPart part, boolean initial, CompositePart component, 
			TreeSet<AtomicPart> allParts, TraversedObjects traversedObjects) {

		traversedObjects.atomicParts.add(part);
		
		DesignObjTest.checkInvariants(part, initial, Parameters.MaxAtomicParts,
				Parameters.MinAtomicDate, Parameters.MaxAtomicDate);
	
		int id = part.getId(), x = part.getX(), y = part.getY();
		if(Math.abs(x - y) != 1)
			reportError(part, id, "inconsistent x and y attributes: x = " + x + ", y = " + y);
		
		if(part.getPartOf() != component)
			reportError(part, id, "invalid reference to CompositePart parent");
		
		ImmutableCollection<Connection> to = part.getToConnections(), from = part.getFromConnections();
		if(to.size() != Parameters.NumConnPerAtomic)
			reportError(part, id, "to", Parameters.NumConnPerAtomic, to.size());
		
		for(Connection connection : from) {
			ConnectionTest.checkInvariants(connection, part);
			
			ImmutableCollection<Connection> sourceToSet = connection.getSource().getToConnections();
			boolean foundMyself = false;
			for(Connection outConn : sourceToSet)
				if(outConn.getSource() == part) {
					foundMyself = true;
					break;
				}
			if(! foundMyself)
				reportError(part, id, "inconsistent 'from' set");
		}
		
		for(Connection connection : to) {
			ConnectionTest.checkInvariants(connection, part);
			
			allParts.add(connection.getDestination());
		}
	}
}
