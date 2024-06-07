package stmbench7.correctness.opacity;

import java.util.HashSet;
import java.util.Iterator;

import stmbench7.OperationId;
import stmbench7.Setup;
import stmbench7.annotations.Immutable;
import stmbench7.annotations.ThreadLocal;
import stmbench7.backend.ImmutableCollection;
import stmbench7.backend.Index;
import stmbench7.backend.LargeSet;
import stmbench7.core.Assembly;
import stmbench7.core.AtomicPart;
import stmbench7.core.BaseAssembly;
import stmbench7.core.ComplexAssembly;
import stmbench7.core.CompositePart;
import stmbench7.core.Connection;
import stmbench7.core.DesignObj;
import stmbench7.core.Document;
import stmbench7.core.Manual;
import stmbench7.core.Module;
import stmbench7.core.Operation;
import stmbench7.core.RuntimeError;

/**
 * An operation that compares two benchmark data structures
 * and throws a RuntimeError if they differ. Used to check
 * whether a concurrent execution ensures opacity.
 */
@Immutable
@ThreadLocal
public class StructureComparisonOperation implements Operation {

	private final Setup setup1, setup2;
	
	public StructureComparisonOperation(Setup setup1, Setup setup2) {
		this.setup1 = setup1;
		this.setup2 = setup2;
	}
	
	public int performOperation() {
		checkModulesEqual();
		checkDesignLibrariesEqual();
		checkIndexesEqual();
		return 0;
	}
	
	private void checkModulesEqual() {
		Module module1 = setup1.getModule(), module2 = setup2.getModule();
		checkReferences(module1, module2, setup1, 0, setup2, 0, "module");
		checkDesignObjEqual(module1, module2);

		int id1 = module1.getId(), id2 = module2.getId();
		Manual man1 = module1.getManual(), man2 = module2.getManual();
		checkReferences(man1, man2, module1, id1, module2, id2, "manual");
		checkManualsEqual(man1, man2);
		
		ComplexAssembly root1 = module1.getDesignRoot(), root2 = module2.getDesignRoot();
		checkReferences(root1, root2, module1, id1, module2, id2, "designRoot");
		checkAssembliesEqual(root1, root2);
	}
	
	private void checkDesignObjEqual(DesignObj obj1, DesignObj obj2) {
		int id1 = obj1.getId(), id2 = obj2.getId();
		checkEqual(id1, id2, obj1, id1, obj2, id2, "id");
		checkEqual(obj1.getType(), obj2.getType(), obj1, id1, obj2, id2, "type");
		checkEqual(obj1.getBuildDate(), obj2.getBuildDate(), obj1, id1, obj2, id2, "buildDate");
	}
	
	private void checkManualsEqual(Manual man1, Manual man2) {
		int id1 = man1.getId(), id2 = man2.getId();
		checkEqual(id1, id2, man1, id1, man2, id2, "id");
		checkEqual(man1.getTitle(), man2.getTitle(), man1, id1, man2, id2, "title");
		checkEqual(man1.getText(), man2.getText(), man1, id1, man2, id2, "text");
		checkReferences(man1.getModule(), man2.getModule(), man1, id1, man2, id2, "module");
	}

	private void checkAssembliesEqual(Assembly assembly1, Assembly assembly2) {
		checkDesignObjEqual(assembly1, assembly2);
		int id1 = assembly1.getId(), id2 = assembly2.getId();
		checkReferences(assembly1.getModule(), assembly2.getModule(),
				assembly1, id1, assembly2, id2, "module");
		checkReferences(assembly1.getSuperAssembly(), assembly2.getSuperAssembly(),
				assembly1, id1, assembly2, id2, "superAssembly");
		
		if(! assembly1.getClass().equals(assembly2.getClass()))
		
		if(assembly1 instanceof ComplexAssembly) {
			if(! (assembly2 instanceof ComplexAssembly))
				reportError(assembly1, id1, assembly2, id2, "objects of different classes");				
			checkComplexAssembliesEqual((ComplexAssembly)assembly1, (ComplexAssembly)assembly2);
		}
		else {
			if(! (assembly2 instanceof BaseAssembly))
				reportError(assembly1, id1, assembly2, id2, "objects of different classes");
			checkBaseAssembliesEqual((BaseAssembly)assembly1, (BaseAssembly)assembly2);
		}
	}
	
	private void checkComplexAssembliesEqual(ComplexAssembly assembly1,
			ComplexAssembly assembly2) {
		int id1 = assembly1.getId(), id2 = assembly2.getId();
		checkEqual(assembly1.getLevel(), assembly2.getLevel(), 
				assembly1, id1, assembly2, id2, "level");
		
		ImmutableCollection<Assembly> subAss1 = assembly1.getSubAssemblies(),
			subAss2 = assembly2.getSubAssemblies();
		checkEqual(subAss1.size(), subAss2.size(),
				assembly1, id1, assembly2, id2, "subAssemblies.size()");
		
		Iterator<Assembly> it1 = subAss1.iterator(), it2 = subAss2.iterator();
		while(it1.hasNext())  {
			Assembly child1 = it1.next(), child2 = it2.next();
			checkReferences(child1, child2, assembly1, id1, assembly2, id2, "subAssemblies");
			checkAssembliesEqual(child1, child2);
		}
	}

	private void checkBaseAssembliesEqual(BaseAssembly assembly1, 
			BaseAssembly assembly2) {
		int id1 = assembly1.getId(), id2 = assembly2.getId();
		ImmutableCollection<CompositePart> comp1 = assembly1.getComponents(),
			comp2 = assembly2.getComponents();
		checkEqual(comp1.size(), comp2.size(), 
				assembly1, id1, assembly2, id2, "components.size()");
		
		Iterator<CompositePart> it1 = comp1.iterator(), it2 = comp2.iterator();
		while(it1.hasNext()) {
			CompositePart component1 = it1.next(), component2 = it2.next();
			checkReferences(component1, component2, 
					assembly1, id1, assembly2, id2, "components");
			checkEqual(component1.getId(), component2.getId(),
					assembly1, id1, assembly2, id2, "components");
		}
	}
	
	private void checkDesignLibrariesEqual() {
		Index<Integer,CompositePart> library1 = setup1.getCompositePartIdIndex(),
			library2 = setup2.getCompositePartIdIndex();
		checkReferences(library1, library2, setup1, 0, setup2, 0, "CompositePart.id index");

		Iterator<CompositePart> it1 = library1.iterator(), it2 = library2.iterator();
		while(it1.hasNext()) {
			if(! it2.hasNext())
				reportError(setup1, 0, setup2, 0, "CompositePart.id index size differences");
			
			CompositePart component1 = it1.next(), component2 = it2.next();
			checkReferences(component1, component2, setup1, 0, setup2, 0, "CompositePart.id index");
			checkCompositePartsEqual(component1, component2);
		}
	}
	
	private void checkCompositePartsEqual(CompositePart component1,
			CompositePart component2) {
		checkDesignObjEqual(component1, component2);
		
		int id1 = component1.getId(), id2 = component2.getId();
		Document doc1 = component1.getDocumentation(), doc2 = component2.getDocumentation();
		checkReferences(doc1, doc2, component1, id1, component2, id2, "documentation");
		checkDocumentsEqual(doc1, doc2);
		
		ImmutableCollection<BaseAssembly> usedIn1 = component1.getUsedIn(),
			usedIn2 = component2.getUsedIn();
		checkEqual(usedIn1.size(), usedIn2.size(),
				component1, id1, component2, id2, "usedIn.size()");
		
		Iterator<BaseAssembly> it1 = usedIn1.iterator(), it2 = usedIn2.iterator();
		while(it1.hasNext()) {
			BaseAssembly assembly1 = it1.next(), assembly2 = it2.next();
			checkReferences(assembly1, assembly2,
					component1, id1, component2, id2, "usedIn");
			checkEqual(assembly1.getId(), assembly2.getId(),
					component1, id1, component2, id2, "usedIn");
		}
		
		AtomicPart root1 = component1.getRootPart(), root2 = component2.getRootPart();
		checkReferences(root1, root2, component1, id1, component2, id2, "rootPart");
		checkEqual(root1.getId(), root2.getId(), component1, id1, component2, id2, "rootPart");
		
		LargeSet<AtomicPart> parts1 = component1.getParts(),
			parts2 = component2.getParts();
		checkReferences(parts1, parts2, component1, id1, component2, id2, "parts");
		checkEqual(parts1.size(), parts2.size(), component1, id1, component2, id2, 
				"parts.size()");

		Iterator<AtomicPart> partsIt1 = parts1.iterator(), partsIt2 = parts2.iterator();
		while(partsIt1.hasNext()) {
			AtomicPart part1 = partsIt1.next(), part2 = partsIt2.next();
			checkReferences(part1, part2, component1, id1, component2, id2, "parts");
			checkAtomicPartsEqual(part1, part2);
		}
	}
	
	private void checkDocumentsEqual(Document doc1, Document doc2) {
		int id1 = doc1.getDocumentId(), id2 = doc2.getDocumentId();
		checkEqual(id1, id2, doc1, id1, doc2, id2, "id");
		checkEqual(doc1.getTitle(), doc2.getTitle(), doc1, id1, doc2, id2, "title");
		checkEqual(doc1.getText(), doc2.getText(), doc1, id1, doc2, id2, "text");
		checkReferences(doc1.getCompositePart(), doc2.getCompositePart(),
				doc1, id1, doc2, id2, "part");
	}
	
	private void checkAtomicPartsEqual(AtomicPart part1, AtomicPart part2) {
		checkDesignObjEqual(part1, part2);
		int id1 = part1.getId(), id2 = part2.getId();
		checkEqual(part1.getX(), part2.getX(), part1, id1, part2, id2, "x");
		checkEqual(part1.getY(), part2.getY(), part1, id1, part2, id2, "y");
		checkReferences(part1.getPartOf(), part2.getPartOf(),
				part1, id1, part2, id2, "partOf");
		
		ImmutableCollection<Connection> to1 = part1.getToConnections(),
			to2 = part2.getToConnections();
		checkEqual(to1.size(), to2.size(), part1, id1, part2, id2, "to.size()");
		Iterator<Connection> toIt1 = to1.iterator(), toIt2 = to2.iterator();
		while(toIt1.hasNext()) {
			Connection conn1 = toIt1.next(), conn2 = toIt2.next();
			checkReferences(conn1, conn2, part1, id1, part2, id2, "to");
			checkConnectionsEqual(conn1, conn2);
		}
	}
	
	private void checkConnectionsEqual(Connection conn1, Connection conn2) {
		checkEqual(conn1.getType(), conn2.getType(), conn1, 0, conn2, 0, "type");
		checkEqual(conn1.getLength(), conn2.getLength(), conn1, 0, conn2, 0, "length");
		
		AtomicPart src1 = conn1.getSource(), src2 = conn2.getSource();
		checkReferences(src1, src2, conn1, 0, conn2, 0, "from");
		checkEqual(src1.getId(), src2.getId(), conn1, 0, conn2, 0, "from");
		
		AtomicPart dest1 = conn1.getDestination(), dest2 = conn2.getDestination();
		checkReferences(dest1, dest2, conn1, 0, conn2, 0, "to");
		checkEqual(dest1.getId(), dest2.getId(), conn1, 0, conn2, 0, "to");
	}
	
	private void checkIndexesEqual() {
	    Index<Integer,AtomicPart> atomicPartIdIndex1 = setup1.getAtomicPartIdIndex(),
	    	atomicPartIdIndex2 = setup2.getAtomicPartIdIndex();
	    checkEqual(atomicPartIdIndex1, atomicPartIdIndex2, "AtomicPart.id");
	    
	    Index<Integer,LargeSet<AtomicPart>> atomicPartBuildDateIndex1 = setup1.getAtomicPartBuildDateIndex(),
	    	atomicPartBuildDateIndex2 = setup2.getAtomicPartBuildDateIndex();
	    checkEqual(atomicPartBuildDateIndex1, atomicPartBuildDateIndex2, "AtomicPart.buildDate");
	    
	    Index<String,Document> documentTitleIndex1 = setup1.getDocumentTitleIndex(),
	    	documentTitleIndex2 = setup2.getDocumentTitleIndex();
	    checkEqual(documentTitleIndex1, documentTitleIndex2, "Document.title");
	    
	    Index<Integer,CompositePart> compositePartIdIndex1 = setup1.getCompositePartIdIndex(),
	    	compositePartIdIndex2 = setup2.getCompositePartIdIndex();
	    checkEqual(compositePartIdIndex1, compositePartIdIndex2, "CompositePart.id");
	    
	    Index<Integer,BaseAssembly> baseAssemblyIdIndex1 = setup1.getBaseAssemblyIdIndex(),
	    	baseAssemblyIdIndex2 = setup2.getBaseAssemblyIdIndex();
	    checkEqual(baseAssemblyIdIndex1, baseAssemblyIdIndex2, "BaseAssembly.id");
	    
	    Index<Integer,ComplexAssembly> complexAssemblyIdIndex1 = setup1.getComplexAssemblyIdIndex(),
	    	complexAssemblyIdIndex2 = setup2.getComplexAssemblyIdIndex();
	    checkEqual(complexAssemblyIdIndex1, complexAssemblyIdIndex2, "ComplexAssembly.id");
	}
	
	@SuppressWarnings("unchecked")
	private void checkEqual(Index index1, Index index2, String indexName) {
		for(Object key1 : index1.getKeys()) {
			Object val1 = index1.get((Comparable) key1);
			Object val2 = index2.get((Comparable) key1);
			if(val2 == null)
				throw new RuntimeError("Indexes " + indexName + ": index2 does not contain key " + key1.toString());
			
			if(val1 instanceof Iterable) {
				checkEqual((Iterable)val1, (Iterable)val2, indexName + " at key " + key1.toString());
				continue;
			}
			
			if(! val1.equals(val2))
				throw new RuntimeError("Indexes " + indexName + ": different values for key " + key1.toString() +
						" --> [" + val1.toString() + "] != [" + val2.toString() + "]");
		}
		for(Object key2 : index2.getKeys()) {
			if(index1.get((Comparable) key2) == null)
				throw new RuntimeError("Indexes " + indexName + ": different number of keys");
		}
	}
	
	@SuppressWarnings("unchecked")
	private void checkEqual(Iterable setIter1, Iterable setIter2, String setName) {
		HashSet set1 = new HashSet(), set2 = new HashSet();
		for(Object obj : setIter1) set1.add(obj);
		for(Object obj : setIter2) set2.add(obj);
		
		for(Object obj1 : setIter1) {
			if(! set2.contains(obj1))
				throw new RuntimeError("Sets " + setName + ": element [" + obj1.toString() + "] not in set2");
		}
		for(Object obj2 : setIter2) {
			if(! set1.contains(obj2))
				throw new RuntimeError("Sets " + setName + ": element [" + obj2.toString() + "] not in set1");
		}
	}
	
	private void reportError(Object obj1, int id1, Object obj2, int id2,
			String message) {
		throw new RuntimeError("Object " + obj1.toString() + " with id = " + id1 +
				" != object " + obj2.toString() + " with id = " + id2 +
				": " + message);
	}
	
	private void checkEqual(int val1, int val2, 
			Object obj1, int id1, Object obj2, int id2, String attribute) {
		if(val1 != val2)
			reportError(obj1, id1, obj2, id2, "attribute " + attribute + " --> " +
					val1 + " != " + val2);
	}

	private void checkEqual(String val1, String val2, 
			Object obj1, int id1, Object obj2, int id2, String attribute) {
		if(! val1.equals(val2))
			reportError(obj1, id1, obj2, id2, "attribute " + attribute + " --> " +
					val1 + " != " + val2);
	}

	private void checkReferences(Object val1, Object val2,
			Object obj1, int id1, Object obj2, int id2, String attribute) {

		if(val1 != null && val1 == val2)
			reportError(obj1, id1, obj2, id2, "attribute " + attribute + " --> " +
					"references equal");
		else if( (val1 == null && val2 != null) || (val1 != null && val2 == null) )
			reportError(obj1, id1, obj2, id2, "attribute " + attribute + " --> " + 
					"one (and only one) reference is null");
	}

	public OperationId getOperationId() {
		return null;
	}
}
