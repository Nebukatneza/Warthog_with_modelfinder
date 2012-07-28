package de.stzoit.prover.collections;

public interface ComparableWithIndex<T> extends Comparable<T> {
	int index();
	void setIndex(int i);
}
