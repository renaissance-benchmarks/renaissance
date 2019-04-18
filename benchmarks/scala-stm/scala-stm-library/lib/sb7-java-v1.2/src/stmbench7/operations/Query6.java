package stmbench7.operations;

import stmbench7.OperationId;
import stmbench7.Setup;
import stmbench7.annotations.ReadOnly;
import stmbench7.annotations.Transactional;
import stmbench7.core.Assembly;
import stmbench7.core.BaseAssembly;
import stmbench7.core.ComplexAssembly;
import stmbench7.core.Module;

/**
 * Query Q6 (see the specification). Read-only, long traversal.
 */
public class Query6 extends Query5 {

	protected Module module;

	public Query6(Setup oo7setup) {
		super(oo7setup);
		this.module = oo7setup.getModule();
	}

	@Override
	@Transactional
	@ReadOnly
	public int performOperation() {
		return checkComplexAssembly(module.getDesignRoot());
	}

	protected int checkAssembly(Assembly assembly) {
		if (assembly instanceof BaseAssembly)
			return checkBaseAssembly((BaseAssembly) assembly);
		else
			return checkComplexAssembly((ComplexAssembly) assembly);
	}

	protected int checkComplexAssembly(ComplexAssembly assembly) {
		int result = 0;

		for (Assembly subAssembly : assembly.getSubAssemblies())
			result += checkAssembly(subAssembly);

		if (result == 0)
			return 0;

		assembly.nullOperation();
		return result + 1;
	}

	@Override
	public OperationId getOperationId() {
		return OperationId.Q6;
	}
}
