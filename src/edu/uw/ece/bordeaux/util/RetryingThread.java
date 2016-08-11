package edu.uw.ece.bordeaux.util;

import java.util.logging.Level;
import java.util.logging.Logger;

public class RetryingThread extends Thread {

	final int maxRetry;
	final static Logger logger = Logger.getLogger(
			RetryingThread.class.getName() + "--" + Thread.currentThread().getName());

	public RetryingThread(int maxRetry) {
		this.maxRetry = maxRetry;
	}

	public RetryingThread() {
		this(0);
	}

	public RetryingThread(Runnable target) {
		super(target);
		this.maxRetry = 0;
	}

	public RetryingThread(Runnable target, int maxRetry) {
		super(target);
		this.maxRetry = maxRetry;
	}

	public RetryingThread(String name) {
		super(name);
		this.maxRetry = 0;
	}

	public RetryingThread(ThreadGroup group, Runnable target) {
		super(group, target);
		this.maxRetry = 0;
	}

	public RetryingThread(ThreadGroup group, String name) {
		super(group, name);
		this.maxRetry = 0;
	}

	public RetryingThread(Runnable target, String name) {
		super(target, name);
		this.maxRetry = 0;
	}

	public RetryingThread(ThreadGroup group, Runnable target, String name) {
		super(group, target, name);
		this.maxRetry = 0;
	}

	public RetryingThread(ThreadGroup group, Runnable target, String name,
			long stackSize) {
		super(group, target, name, stackSize);
		this.maxRetry = 0;
	}

	public void run() {

		int retry = 1;

		while (!Thread.currentThread().isInterrupted()) {
			if (retry > maxRetry) {
				throw new RuntimeException("Constantly interrupted. After " + retry
						+ "'th The thread is terminated!");
			}
			try {
				super.run();
				// reset the retry counter
				retry = 1;
			} catch (Throwable e) {
				e.printStackTrace();
				logger
						.log(Level.SEVERE,
								"[" + Thread.currentThread().getName() + "]"
										+ "Executing command is failed for " + retry + "'th time.",
								e);
				retry++;
			}
		}
	}

}
