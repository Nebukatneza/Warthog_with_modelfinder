package de.stzoit.prover;

public class TimeOutException extends Exception {
	private static final long serialVersionUID = 1L;

	public TimeOutException(String msg) {
		super(msg);
	}
}
