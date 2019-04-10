package stmbench7.impl.core;

import stmbench7.core.AtomicPart;
import stmbench7.core.BaseAssembly;
import stmbench7.core.ComplexAssembly;
import stmbench7.core.CompositePart;
import stmbench7.core.Connection;
import stmbench7.core.DesignObjFactory;
import stmbench7.core.Document;
import stmbench7.core.Manual;
import stmbench7.core.Module;

/**
 * Implements methods that create objects implementing
 * interfaces defined in stmbench7.core. This default implementation 
 * constructs objects that are NOT thread-safe. 
 */
public class DesignObjFactoryImpl extends DesignObjFactory {

	@Override
	public AtomicPart createAtomicPart(int id, String type, int buildDate, int x, int y) {
		return new AtomicPartImpl(id, type, buildDate, x, y);
	}

	@Override
	public Connection createConnection(AtomicPart from, AtomicPart to,
			String type, int length) {
		return new ConnectionImpl(from, to, type, length);
	}

	@Override
	public BaseAssembly createBaseAssembly(int id, String type, int buildDate, 
			Module module, ComplexAssembly superAssembly) {
		return new BaseAssemblyImpl(id, type, buildDate, module, superAssembly);
	}
	
	@Override
	public ComplexAssembly createComplexAssembly(int id, String type, int buildDate, 
			Module module, ComplexAssembly superAssembly) {
		return new ComplexAssemblyImpl(id, type, buildDate, module, superAssembly);
	}
	
	@Override
	public CompositePart createCompositePart(int id, String type, int buildDate, 
			Document documentation) {
		return new CompositePartImpl(id, type, buildDate, documentation);
	}
	
	@Override
	public Document createDocument(int id, String title, String text) {
		return new DocumentImpl(id, title, text);
	}
	
	@Override
	public Manual createManual(int id, String title, String text) {
		return new ManualImpl(id, title, text);
	}
	
	@Override
	public Module createModule(int id, String type, int buildDate, Manual man) {
		return new ModuleImpl(id, type, buildDate, man);
	}
}
