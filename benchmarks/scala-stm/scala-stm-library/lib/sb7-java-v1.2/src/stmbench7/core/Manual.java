package stmbench7.core;

import stmbench7.annotations.Atomic;
import stmbench7.annotations.ReadOnly;
import stmbench7.annotations.Update;

/**
 * Part of the main benchmark data structure. For a default
 * implementation, see stmbench7.impl.core.ManualImpl.
 */
@Atomic
public interface Manual {

	@ReadOnly
	int getId();
	
	@ReadOnly
	String getTitle();
	
	@ReadOnly
	String getText();
	
	@ReadOnly
	Module getModule();
	
	@Update
	void setModule(Module module);

	@ReadOnly
	int countOccurences(char ch);

	@ReadOnly
	int checkFirstLastCharTheSame();

	@ReadOnly
	boolean startsWith(char ch);

	@Update
	int replaceChar(char from, char to);
}