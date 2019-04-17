package stmbench7.core;

import stmbench7.Parameters;
import stmbench7.annotations.Immutable;
import stmbench7.backend.BackendFactory;
import stmbench7.backend.IdPool;
import stmbench7.backend.ImmutableCollection;
import stmbench7.backend.Index;

/**
 * Used to create and destroy assembly elements while
 * maintaining the consistency of the data structure
 * and the indexes.
 */
@Immutable
public class AssemblyBuilder extends DesignObjBuilder {

	private final IdPool baseAssemblyIdPool, complexAssemblyIdPool; 

	private final Index<Integer,BaseAssembly> baseAssemblyIdIndex;
	private final Index<Integer,ComplexAssembly> complexAssemblyIdIndex;
	
	public AssemblyBuilder(Index<Integer,BaseAssembly> baseAssemblyIdIndex,
			Index<Integer,ComplexAssembly> complexAssemblyIdIndex) {
		this.baseAssemblyIdIndex = baseAssemblyIdIndex;
		baseAssemblyIdPool = BackendFactory.instance.createIdPool(Parameters.MaxBaseAssemblies);
		
		this.complexAssemblyIdIndex = complexAssemblyIdIndex;
		complexAssemblyIdPool = BackendFactory.instance.createIdPool(Parameters.MaxComplexAssemblies);
	}
	
	public Assembly createAndRegisterAssembly(Module module, ComplexAssembly superAssembly) 
			throws OperationFailedException {
		if( (superAssembly == null) || (superAssembly.getLevel() > 2) )
			return createAndRegisterComplexAssembly(module, superAssembly);
		
		return createAndRegisterBaseAssembly(module, superAssembly);
	}
	
	public void unregisterAndRecycleAssembly(Assembly assembly) {
		if(assembly instanceof ComplexAssembly)
			unregisterAndRecycleComplexAssembly((ComplexAssembly)assembly);
		else unregisterAndRecycleBaseAssembly((BaseAssembly)assembly);
	}
	
	public void unregisterAndRecycleBaseAssembly(BaseAssembly baseAssembly) {
		int baseAssemblyId = baseAssembly.getId();
		baseAssemblyIdIndex.remove(baseAssemblyId);
		
		baseAssembly.getSuperAssembly().removeSubAssembly(baseAssembly);
		
		ImmutableCollection<CompositePart> componentsSet = baseAssembly.getComponents().clone();
		for(CompositePart component : componentsSet)
			baseAssembly.removeComponent(component);

		baseAssembly.clearPointers();
		baseAssemblyIdPool.putUnusedId(baseAssemblyId);
	}

	public void unregisterAndRecycleComplexAssembly(ComplexAssembly complexAssembly) {
		short currentLevel = complexAssembly.getLevel();
		ComplexAssembly superAssembly = complexAssembly.getSuperAssembly();
		
		if(superAssembly == null) 
			throw new RuntimeError("ComplexAssemblyFactory: root Complex Assembly cannot be removed!");
		
		superAssembly.removeSubAssembly(complexAssembly);
		
		ImmutableCollection<Assembly> subAssembliesSet = complexAssembly.getSubAssemblies().clone();
		for(Assembly assembly : subAssembliesSet) {
			if(currentLevel > 2) unregisterAndRecycleComplexAssembly((ComplexAssembly)assembly);
			else unregisterAndRecycleBaseAssembly((BaseAssembly)assembly);
		}
		
		int id = complexAssembly.getId();
		complexAssemblyIdIndex.remove(id);

		complexAssembly.clearPointers();
		complexAssemblyIdPool.putUnusedId(id);
	}
	
	private BaseAssembly createAndRegisterBaseAssembly(Module module, ComplexAssembly superAssembly)
			throws OperationFailedException {
		int date = createBuildDate(Parameters.MinAssmDate, Parameters.MaxAssmDate);
		int assemblyId = baseAssemblyIdPool.getId();
		BaseAssembly baseAssembly = 
			designObjFactory.createBaseAssembly(assemblyId, createType(), date, module, superAssembly);
		
		baseAssemblyIdIndex.put(assemblyId, baseAssembly);

		superAssembly.addSubAssembly(baseAssembly);

		return baseAssembly;
	}

	private ComplexAssembly createAndRegisterComplexAssembly(Module module, ComplexAssembly superAssembly) 
			throws OperationFailedException {
		int id = complexAssemblyIdPool.getId();
		int date = createBuildDate(Parameters.MinAssmDate, Parameters.MaxAssmDate);
		ComplexAssembly complexAssembly = 
			designObjFactory.createComplexAssembly(id, createType(), date, module, superAssembly);

		try {
			for(int i = 0; i < Parameters.NumAssmPerAssm; i++) 
				createAndRegisterAssembly(module, complexAssembly);
		}
		catch(OperationFailedException e) {
			for(Assembly subAssembly : complexAssembly.getSubAssemblies().clone())
				unregisterAndRecycleAssembly(subAssembly);
			complexAssemblyIdPool.putUnusedId(id);
			complexAssembly.clearPointers();
			throw e;
		}
		
		complexAssemblyIdIndex.put(id, complexAssembly);
		
		if(superAssembly != null) superAssembly.addSubAssembly(complexAssembly);
		
		return complexAssembly;
	}
}
