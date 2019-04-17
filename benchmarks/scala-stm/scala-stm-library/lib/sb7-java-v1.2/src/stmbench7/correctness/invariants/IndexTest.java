package stmbench7.correctness.invariants;

import java.util.HashSet;

import stmbench7.Setup;
import stmbench7.annotations.Immutable;
import stmbench7.annotations.ThreadLocal;
import stmbench7.backend.Index;
import stmbench7.backend.LargeSet;
import stmbench7.core.AtomicPart;
import stmbench7.core.BaseAssembly;
import stmbench7.core.ComplexAssembly;
import stmbench7.core.CompositePart;
import stmbench7.core.Document;
import stmbench7.core.RuntimeError;

/**
 * Test of invariants of indexes, and their consistency
 * with the main data structure. Checks also invariants
 * of the composite parts that are not reachable from
 * base assemblies.
 */
@Immutable
@ThreadLocal
public class IndexTest extends InvariantTest {

	public static void checkInvariants(Setup setup, boolean initial, TraversedObjects traversedObjects) {

		// Complex assemblies
		Index<Integer,ComplexAssembly> complexAssemblyIdIndex = setup.getComplexAssemblyIdIndex();
		for(ComplexAssembly traversedAssembly : traversedObjects.complexAssemblies) {
			int id = traversedAssembly.getId();
			ComplexAssembly indexedAssembly = complexAssemblyIdIndex.get(id);
			checkIndexValue("ComplexAssembly.id", traversedAssembly, indexedAssembly, id);
		}	
		checkAllTraversed(complexAssemblyIdIndex, traversedObjects.complexAssemblies, "ComplexAssembly.id");
		traversedObjects.complexAssemblies.clear();
		
		// Base assemblies
		Index<Integer,BaseAssembly> baseAssemblyIdIndex = setup.getBaseAssemblyIdIndex();
		for(BaseAssembly traversedAssembly : traversedObjects.baseAssemblies) {
			int id = traversedAssembly.getId();
			BaseAssembly indexedAssembly = baseAssemblyIdIndex.get(id);
			checkIndexValue("BaseAssembly.id", traversedAssembly, indexedAssembly, id);
		}
		checkAllTraversed(baseAssemblyIdIndex, traversedObjects.baseAssemblies, "BaseAssembly.id");	
		traversedObjects.baseAssemblies.clear();
		
		// Composite parts
		Index<Integer,CompositePart> compositePartIdIndex = setup.getCompositePartIdIndex();
		for(CompositePart traversedComponent : traversedObjects.components) {
			int id = traversedComponent.getId();
			CompositePart indexedComponent = compositePartIdIndex.get(id);
			checkIndexValue("CompositePart.id", traversedComponent, indexedComponent, id);
		}
		
		// Check invariants for components disconnected from the data structure
		// (and add those components to the set of traversed objects)
		for(CompositePart indexedComponent : compositePartIdIndex)
			if(! traversedObjects.components.contains(indexedComponent))
				CompositePartTest.checkInvariants(indexedComponent, initial, null, traversedObjects);
		traversedObjects.components.clear();
		
		// Documents
	    Index<String,Document> documentTitleIndex = setup.getDocumentTitleIndex();
	    for(Document traversedDocument : traversedObjects.documents) {
	    	String title = traversedDocument.getTitle();
	    	int id = traversedDocument.getDocumentId();
	    	
	    	Document indexedDocument = documentTitleIndex.get(title);
	    	checkIndexValue("Document.title", traversedDocument, indexedDocument, id);
	    }
	    checkAllTraversed(documentTitleIndex, traversedObjects.documents, "Document.title");
	    traversedObjects.documents.clear();
	    
	    // Atomic parts (id index)
		Index<Integer,AtomicPart> atomicPartIdIndex = setup.getAtomicPartIdIndex();
	    for(AtomicPart traversedPart : traversedObjects.atomicParts) {
	    	int id = traversedPart.getId();
	    	
	    	AtomicPart indexedPart = atomicPartIdIndex.get(id);
	    	checkIndexValue("AtomicPart.id", traversedPart, indexedPart, id);
	    }
	    checkAllTraversed(atomicPartIdIndex, traversedObjects.atomicParts, "AtomicPart.id");
	    
	    // Atomic parts (buildDate index)
	    Index<Integer,LargeSet<AtomicPart>> atomicPartBuildDateIndex = setup.getAtomicPartBuildDateIndex();
	    for(AtomicPart traversedPart : traversedObjects.atomicParts) {
	    	int id = traversedPart.getId();
	    	LargeSet<AtomicPart> sameBuildDateParts = 
	    		atomicPartBuildDateIndex.get(traversedPart.getBuildDate());
	    	if(sameBuildDateParts == null || !sameBuildDateParts.contains(traversedPart))
	    		reportError("AtomicPart.buildDate", "element with id = " + id + " not in the index");
	    }

	    for(LargeSet<AtomicPart> sameBuildDateParts : atomicPartBuildDateIndex)
	    	for(AtomicPart indexedPart : sameBuildDateParts)
	    		if(! traversedObjects.atomicParts.contains(indexedPart))
	    			reportError("AtomicPart.buildDate", "index contains too many elements");
	    traversedObjects.atomicParts.clear();
	}
	
	private static void reportError(String index, String message) {
		throw new RuntimeError("Index " + index + ": " + message);
	}
	
	private static void checkIndexValue(String index, Object traversedObject, Object indexedObject, int elementId) {
    	if(indexedObject == null)		
    		reportError(index, "element with id = " + elementId + 
    				" in the data structure but not in the index");
    	if(indexedObject != traversedObject)
    		reportError(index, "element with id = "	+ elementId +
    				" is a different object in the index and in the data structure");
	}
	
	private static void checkAllTraversed(Index<?,?> index, HashSet<?> traversedSet, String indexName) {
	    for(Object indexedObject : index)
	    	if(! traversedSet.contains(indexedObject))
	    		reportError(indexName, "index contains too many elements (element " + indexedObject.toString() + ")");
	}
}
