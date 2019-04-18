package stmbench7.core;

import stmbench7.Parameters;
import stmbench7.annotations.Immutable;
import stmbench7.backend.BackendFactory;
import stmbench7.backend.IdPool;
import stmbench7.backend.Index;

/**
 * Used to create a module element with the default initial 
 * data structure underneath. Calls other builder classes
 * to construct respective elements of the structure.
 */
@Immutable
public class ModuleBuilder extends DesignObjBuilder {

	private final IdPool idPool;
	private final ManualBuilder manualFactory;
	private final AssemblyBuilder assemblyBuilder;
	
	public ModuleBuilder(Index<Integer,BaseAssembly> baseAssemblyIdIndex,
			Index<Integer,ComplexAssembly> complexAssemblyIdIndex) {
		manualFactory = new ManualBuilder();
		assemblyBuilder = new AssemblyBuilder(baseAssemblyIdIndex,
				complexAssemblyIdIndex);
		idPool = BackendFactory.instance.createIdPool(Parameters.NumModules);
	}
	
	public Module createRegisterModule() throws OperationFailedException {
		int moduleId = idPool.getId();
		Manual manual = manualFactory.createManual(moduleId);
		String type = createType();
		int buildDate = createBuildDate(Parameters.MinModuleDate, Parameters.MaxModuleDate);
		
		Module module = designObjFactory.createModule(moduleId, type, buildDate, manual);
		
		ComplexAssembly designRoot = (ComplexAssembly) assemblyBuilder.createAndRegisterAssembly(module, null);
		module.setDesignRoot(designRoot);
		
		return module;
	}
	
	public AssemblyBuilder getAssemblyBuilder() {
		return assemblyBuilder;
	}
}
