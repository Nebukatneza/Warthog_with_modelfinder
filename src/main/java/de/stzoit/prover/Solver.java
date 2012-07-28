package de.stzoit.prover;

import de.stzoit.prover.cnf.Clause;

public interface Solver {
	public boolean pushClause(Clause clause) throws Exception;
	public void save() throws Exception;
	public void pop() throws Exception;
	public boolean sat() throws Exception;
	public Model getModel() throws Exception;
	public void reset() throws Exception;
}
