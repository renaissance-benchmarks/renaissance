package stmbench7.core;

import stmbench7.Parameters;
import stmbench7.annotations.Immutable;
import stmbench7.backend.BackendFactory;
import stmbench7.backend.IdPool;

/**
 * Used to create a manual element that conforms to the
 * benchmark specification.
 */
@Immutable
public class ManualBuilder extends DesignObjBuilder {

	private final IdPool idPool;
	
	public ManualBuilder() {
		idPool = BackendFactory.instance.createIdPool(Parameters.NumModules);
	}
	
	public Manual createManual(int moduleId) throws OperationFailedException {
		int manualId = idPool.getId();
		String title = "Manual for module #" + moduleId;
		String text = createText(Parameters.ManualSize, "I am the manual for module #" + moduleId + "\n");
		
		return designObjFactory.createManual(manualId, title, text);
	}
}
