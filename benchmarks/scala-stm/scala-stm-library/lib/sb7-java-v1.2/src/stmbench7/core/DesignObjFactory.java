package stmbench7.core;

import stmbench7.annotations.Immutable;

/**
 * A factory for creating all the objects of the main benchmark
 * data structure. A default implementation is provided by the
 * stmbench7.impl.core.DesignObjFactoryImpl class, but most STM
 * implementations will provide their own implementation, which
 * will create transaction-safe versions of the data structure
 * elements.
 */
@Immutable
public abstract class DesignObjFactory {

	public static DesignObjFactory instance = null;
	
	public static void setInstance(DesignObjFactory newInstance) {
		instance = newInstance;
	}
	
	public abstract AtomicPart createAtomicPart(int id, String type, int buildDate, int x, int y);
	public abstract Connection createConnection(AtomicPart from, AtomicPart to, String type, int length);
	public abstract BaseAssembly createBaseAssembly(int id, String type, int buildDate, 
			Module module, ComplexAssembly superAssembly);
	public abstract ComplexAssembly createComplexAssembly(int id, String type, int buildDate, 
			Module module, ComplexAssembly superAssembly);
	public abstract CompositePart createCompositePart(int id, String type, int buildDate, 
			Document documentation);
	public abstract Document createDocument(int id, String title, String text);
	public abstract Manual createManual(int id, String title, String text);
	public abstract Module createModule(int id, String type, int buildDate, Manual man);	
}
