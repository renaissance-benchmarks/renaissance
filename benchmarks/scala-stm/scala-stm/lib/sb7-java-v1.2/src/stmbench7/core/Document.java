package stmbench7.core;

import stmbench7.annotations.Atomic;
import stmbench7.annotations.ReadOnly;
import stmbench7.annotations.Update;

/**
 * Part of the main benchmark data structure. For a default
 * implementation, see stmbench7.impl.core.DocumentImpl.
 */
@Atomic
public interface Document {

	@Update
	void setPart(CompositePart part);

	@ReadOnly
	CompositePart getCompositePart();

	@ReadOnly
	int getDocumentId();

	@ReadOnly
	String getTitle();

	@ReadOnly
	void nullOperation();

	@ReadOnly
	int searchText(char symbol);

	@Update
	int replaceText(String from, String to);

	@ReadOnly
	boolean textBeginsWith(String prefix);

	@ReadOnly
	String getText();
}
