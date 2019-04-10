package stmbench7.correctness.invariants;

import stmbench7.Parameters;
import stmbench7.annotations.Immutable;
import stmbench7.annotations.ThreadLocal;
import stmbench7.core.AtomicPart;
import stmbench7.core.Connection;

/**
 * Test of invariants of a connection.
 */
@Immutable
@ThreadLocal
public class ConnectionTest extends InvariantTest {

	public static void checkInvariants(Connection connection, AtomicPart from) {

		if(! DesignObjTest.checkType(connection.getType()))
			reportError(connection, 0, "type", "type #...", connection.getType());
		
		int length = connection.getLength();
		if(length < 1 || length > Parameters.XYRange)
			reportError(connection, 0, "length", 1, Parameters.XYRange, length);
		
		if(connection.getSource() != from)
			reportError(connection, 0, "invalid source (from) reference");
	}
}
