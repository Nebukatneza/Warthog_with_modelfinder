package de.stzoit.prover;

import java.util.List;

import de.stzoit.prover.cnf.Variable;

public interface Model {
	void pushPositive(Variable variable);
	void pushNegative(Variable variable);
	String getConjunction(String and, String not);
	List<String> getPositiveNames();
	List<String> getNegativeNames();
}
