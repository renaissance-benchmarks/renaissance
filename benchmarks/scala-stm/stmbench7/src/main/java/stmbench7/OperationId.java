package stmbench7;

import stmbench7.annotations.NonAtomic;
import stmbench7.core.Operation;
import stmbench7.operations.Operation10;
import stmbench7.operations.Operation11;
import stmbench7.operations.Operation12;
import stmbench7.operations.Operation13;
import stmbench7.operations.Operation14;
import stmbench7.operations.Operation15;
import stmbench7.operations.Operation6;
import stmbench7.operations.Operation7;
import stmbench7.operations.Operation8;
import stmbench7.operations.Operation9;
import stmbench7.operations.Query1;
import stmbench7.operations.Query2;
import stmbench7.operations.Query3;
import stmbench7.operations.Query4;
import stmbench7.operations.Query5;
import stmbench7.operations.Query6;
import stmbench7.operations.Query7;
import stmbench7.operations.ShortTraversal1;
import stmbench7.operations.ShortTraversal10;
import stmbench7.operations.ShortTraversal2;
import stmbench7.operations.ShortTraversal6;
import stmbench7.operations.ShortTraversal7;
import stmbench7.operations.ShortTraversal8;
import stmbench7.operations.ShortTraversal9;
import stmbench7.operations.StructuralModification1;
import stmbench7.operations.StructuralModification2;
import stmbench7.operations.StructuralModification3;
import stmbench7.operations.StructuralModification4;
import stmbench7.operations.StructuralModification5;
import stmbench7.operations.StructuralModification6;
import stmbench7.operations.StructuralModification7;
import stmbench7.operations.StructuralModification8;
import stmbench7.operations.Traversal1;
import stmbench7.operations.Traversal2a;
import stmbench7.operations.Traversal2b;
import stmbench7.operations.Traversal2c;
import stmbench7.operations.Traversal3a;
import stmbench7.operations.Traversal3b;
import stmbench7.operations.Traversal3c;
import stmbench7.operations.Traversal4;
import stmbench7.operations.Traversal5;
import stmbench7.operations.Traversal6;
import stmbench7.operations.Traversal7;
import stmbench7.operations.Traversal8;
import stmbench7.operations.Traversal9;

/**
 * Lists all STMBench7 operations, together with the classes implementing them
 * and their types.
 */
@NonAtomic
public enum OperationId {
	T1(Traversal1.class, OperationType.TRAVERSAL_RO), 
	T2a(Traversal2a.class, OperationType.TRAVERSAL),
	T2b(Traversal2b.class, OperationType.TRAVERSAL),
	T2c(Traversal2c.class, OperationType.TRAVERSAL),
	T3a(Traversal3a.class, OperationType.TRAVERSAL),
	T3b(Traversal3b.class, OperationType.TRAVERSAL),
	T3c(Traversal3c.class, OperationType.TRAVERSAL),
	T4(Traversal4.class, OperationType.TRAVERSAL_RO),
	T5(Traversal5.class, OperationType.TRAVERSAL),
	T6(Traversal6.class, OperationType.TRAVERSAL_RO),
	Q6(Query6.class, OperationType.TRAVERSAL_RO),
	Q7(Query7.class, OperationType.TRAVERSAL_RO),
	
	ST1(ShortTraversal1.class, OperationType.SHORT_TRAVERSAL_RO),
	ST2(ShortTraversal2.class, OperationType.SHORT_TRAVERSAL_RO),
	ST3(Traversal7.class, OperationType.SHORT_TRAVERSAL_RO),
	ST4(Query4.class, OperationType.SHORT_TRAVERSAL_RO),
	ST5(Query5.class, OperationType.SHORT_TRAVERSAL_RO),
	ST6(ShortTraversal6.class, OperationType.SHORT_TRAVERSAL),
	ST7(ShortTraversal7.class, OperationType.SHORT_TRAVERSAL),
	ST8(ShortTraversal8.class, OperationType.SHORT_TRAVERSAL),
	ST9(ShortTraversal9.class, OperationType.SHORT_TRAVERSAL_RO),
	ST10(ShortTraversal10.class, OperationType.SHORT_TRAVERSAL),
	
	OP1(Query1.class, OperationType.OPERATION_RO),
	OP2(Query2.class, OperationType.OPERATION_RO),
	OP3(Query3.class, OperationType.OPERATION_RO),
	OP4(Traversal8.class, OperationType.OPERATION_RO),
	OP5(Traversal9.class, OperationType.OPERATION_RO),
	OP6(Operation6.class, OperationType.OPERATION_RO),
	OP7(Operation7.class, OperationType.OPERATION_RO),
	OP8(Operation8.class, OperationType.OPERATION_RO),
	OP9(Operation9.class, OperationType.OPERATION),
	OP10(Operation10.class, OperationType.OPERATION),
	OP11(Operation11.class, OperationType.OPERATION),
	OP12(Operation12.class, OperationType.OPERATION),
	OP13(Operation13.class, OperationType.OPERATION),
	OP14(Operation14.class, OperationType.OPERATION),
	OP15(Operation15.class, OperationType.OPERATION),
	
	SM1(StructuralModification1.class, OperationType.STRUCTURAL_MODIFICATION),
	SM2(StructuralModification2.class, OperationType.STRUCTURAL_MODIFICATION),
	SM3(StructuralModification3.class, OperationType.STRUCTURAL_MODIFICATION),
	SM4(StructuralModification4.class, OperationType.STRUCTURAL_MODIFICATION),
	SM5(StructuralModification5.class, OperationType.STRUCTURAL_MODIFICATION),
	SM6(StructuralModification6.class, OperationType.STRUCTURAL_MODIFICATION),
	SM7(StructuralModification7.class, OperationType.STRUCTURAL_MODIFICATION),
	SM8(StructuralModification8.class, OperationType.STRUCTURAL_MODIFICATION);

	protected Class<? extends Operation> operationClass;
	protected OperationType type;
	
	private OperationId(Class<? extends Operation> operationClass, OperationType type) {
		this.operationClass = operationClass;
		this.type = type;
	}
	
	public OperationType getType() {
		return type;
	}
	
	public Class<? extends Operation> getOperationClass() {
		return operationClass;
	}
}
