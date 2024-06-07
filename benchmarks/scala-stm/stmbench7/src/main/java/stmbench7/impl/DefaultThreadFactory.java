package stmbench7.impl;

import stmbench7.ThreadFactory;

public class DefaultThreadFactory extends ThreadFactory {

	@Override
	public Thread createThread(Runnable runnable) {
		return new Thread(runnable);
	}
}
