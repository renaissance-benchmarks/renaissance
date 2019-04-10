package stmbench7.correctness.invariants;

import stmbench7.Parameters;
import stmbench7.annotations.Immutable;
import stmbench7.annotations.ThreadLocal;
import stmbench7.core.CompositePart;
import stmbench7.core.Document;

/**
 * Test of invariants of a documentation element.
 */
@Immutable
@ThreadLocal
public class DocumentationTest extends InvariantTest {

	public static void checkInvariants(Document documentation,
			CompositePart component, TraversedObjects traversedObjects) {

		traversedObjects.documents.add(documentation);
		
		int id = documentation.getDocumentId();
		if(id < 1 || id > Parameters.MaxCompParts)
			reportError(documentation, id, "id", 1, Parameters.MaxCompParts, id);
		
		if(documentation.getCompositePart() != component)
			reportError(documentation, id, "invalid reference to CompositePart parent");
		
		String title = documentation.getTitle(),
			titleShouldBe = "Composite Part #" + component.getId();
		if(! title.equals(titleShouldBe))
			reportError(documentation, id, "title", titleShouldBe, title);
		
		String text = documentation.getText();
		if(!text.startsWith("I am the documentation for composite part #" + component.getId()) &&
				!text.startsWith("This is the documentation for composite part #" + component.getId()) )
			reportError(documentation, id, "text (prefix)", "I am / This is the documentation for composite part #...",
					text.substring(0, 30));
	}
}
