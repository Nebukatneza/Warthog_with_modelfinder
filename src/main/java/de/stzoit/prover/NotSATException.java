package de.stzoit.prover;

public class NotSATException extends Exception {
	private static final long serialVersionUID = 1L;

	public NotSATException(String msg) {
		super(msg);
	}
}
